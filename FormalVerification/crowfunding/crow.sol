pragma solidity >=0.4.25 <0.9.0;

contract Crowdfunding {
    address payable owner;
    uint max_block;
    uint goal;

    mapping(address => uint) backers;
    bool funded = false;
    uint blockNumber;
    uint backersCount = 0; // Added to track number of backers

    constructor(address payable _owner, uint _max_block, uint _goal, uint _blockNumber) public {
        owner = _owner;
        max_block = _max_block;
        goal = _goal;
        blockNumber = _blockNumber;
    }

    function Donate(uint n) public payable {
        require(max_block > blockNumber);
        require(backers[msg.sender] == 0);
        backers[msg.sender] = msg.value;
        if (msg.value > 0) {
            backersCount++; // Increment backers count
        }
        t(n);
    }

    function GetFunds(uint p) public {
        require(max_block < blockNumber && msg.sender == owner);
        require(goal <= address(this).balance);
        
        funded = true;
        owner.transfer(address(this).balance);
        t(p);
    }

    function Claim(uint q) public {
        require(blockNumber > max_block);
        require(backers[msg.sender] != 0 && !funded && goal > address(this).balance);
        
        backersCount--; // Decrement backers count
        uint val = backers[msg.sender];
        backers[msg.sender] = 0;
        payable(msg.sender).transfer(val); // added payable
        t(q);
    }

    function t(uint _n) internal {
        blockNumber = blockNumber + _n;
    }
}
import Blaster

abbrev Addr := String
abbrev Amount := Int
abbrev Time := Int

structure Account where
  addr : Addr
  bal : Amount
  deriving Repr, BEq

abbrev Backers := List Account

structure Campaign where
  owner : Account
  maxTime : Time
  goal : Amount
  funded : Bool
  backers : Backers
  backersCount : Int
  totalRaised : Amount
  deriving Repr

structure ActionResult where
  campaign : Campaign
  actor : Account
  deriving Repr

def donate (donor : Account) (campaign : Campaign) (currentTime : Time) (amt : Amount) : Option ActionResult :=
  if campaign.backers.any (fun b => b.addr == donor.addr) then
    none
  else if currentTime >= campaign.maxTime then
    none
  else if campaign.funded then
    none
  else if donor.bal < amt then
    none
  else if amt <= 0 then
    none
  else
    let backer : Account := { donor with bal := amt }
    some {
      campaign := {
        campaign with
        backers := campaign.backers ++ [backer],
        backersCount := campaign.backersCount + 1,
        totalRaised := campaign.totalRaised + amt
      },
      actor := { donor with bal := donor.bal - amt }
    }


def getFunds (claimer : Account) (campaign : Campaign) (currentTime : Time) : Option ActionResult :=
  if currentTime <= campaign.maxTime then
    none
  else if claimer.addr != campaign.owner.addr then
    none
  else if campaign.totalRaised < campaign.goal then
    none
  else if campaign.funded then
    none
  else
    some {
      campaign := { campaign with funded := true },
      actor := { claimer with bal := claimer.bal + campaign.totalRaised }
    }

def claim (claimer : Account) (campaign : Campaign) (currentTime : Time) : Option ActionResult :=
  if currentTime <= campaign.maxTime then
    none
  else if claimer.addr == campaign.owner.addr then
    none
  else if campaign.totalRaised < campaign.goal then
    none
  else if campaign.funded then
    none
  else if !campaign.backers.any (fun b => b.addr == claimer.addr) then
    none
  else
    let backer := (campaign.backers.find? (fun b => b.addr == claimer.addr)).getD { addr := claimer.addr, bal := 0 }
    let amtDonatedByClaimer := backer.bal
    some {
      campaign := {
        campaign with
        backersCount := campaign.backersCount - 1,
        backers := campaign.backers.filter (fun b => b.addr != claimer.addr)
      },
      actor := { claimer with bal := claimer.bal + amtDonatedByClaimer }
    }

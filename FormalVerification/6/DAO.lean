import Mathlib
import Blaster

abbrev Addr := String
abbrev Amount := Int

structure Account where
  addr : Addr
  bal : Amount
  deriving Repr

namespace Account

def valid (acc : Account) : Prop := acc.bal >= 0

end Account

abbrev Ledger := List Account

namespace Ledger

def noneg (ledger : Ledger) : Prop := ledger.Forall (fun x => x.bal >= 0)

def addAccount (ledger : Ledger) (acc : Account) : Ledger :=
  if ledger.any (fun x => x.addr == acc.addr) then
    ledger
  else if acc.bal < 0 then
    ledger
  else acc :: ledger

lemma addAccount_length
  (ledger : Ledger) (acc : Account) :
  acc ∈ ledger -> List.length (ledger.addAccount acc) = List.length ledger := by
  intro hmem
  simp [addAccount]
  split_ifs with hex hpos <;> simp
  exact hex ⟨acc, hmem, rfl⟩

lemma addAccount_preserves_noneg (ledger : Ledger) (acc : Account) :
  ledger.noneg -> (ledger.addAccount acc).noneg := by
  intro hnoneg
  simp [addAccount]
  split_ifs with hex hpos <;> simp_all [noneg]

def getBalance (ledger : Ledger) (name : Addr) : Option Amount := do
  let acc <- ledger.find? (λ x => x.addr == name)
  return acc.bal
 
def getSupply (ledger : Ledger) : Amount := (ledger.map (λ x => x.bal)).sum

def debitAccount (ledger : Ledger) (addr : Addr) (amt : Amount) : Option Ledger :=
  match ledger with    
  | [] => none
  | h :: t =>
      if (h.addr == addr) then
        if (amt <= h.bal) then
          some ({ h with bal := h.bal - amt } :: t)
        else none
      else do
        let ledger' <- debitAccount t addr amt
        return (h :: ledger')

lemma debitAccount_subtracts_supply (ledger : Ledger) (addr : Addr) (amt : Amount) :
  ∀ ledger', ledger.debitAccount addr amt = some ledger'
  -> ledger'.getSupply = ledger.getSupply - amt := by
  induction ledger with
  | nil => simp [debitAccount]
  | cons x xs xih =>
    simp [debitAccount, getSupply] at ⊢ xih
    split
    next => split <;> simp_all; ring
    next =>
      cases h : debitAccount xs addr amt with
      | none    => simp
      | some ys =>
        simp [Option.bind]
        rw [ xih ys h ]
        ring

lemma debitAccount_preserves_noneg (ledger : Ledger) (addr : Addr) (amt : Amount) :
  ∀ ledger', ledger.noneg
  -> ledger.debitAccount addr amt = some ledger'
  -> ledger'.noneg := by
  induction ledger with
  | nil => simp [debitAccount, noneg]
  | cons x xs xih =>
    intro ledger' hnoneg hdebit
    simp [debitAccount] at hdebit
    simp [noneg] at hnoneg
    obtain ⟨hnonegx, hnonegxs⟩ := hnoneg
    by_cases haddr : x.addr = addr
    next =>
      simp [haddr] at hdebit
      obtain ⟨hamt, hledger⟩ := hdebit
      subst hledger
      simp [noneg]
      exact ⟨hamt, hnonegxs⟩
    next =>
      simp [haddr] at hdebit
      cases hdebit' : debitAccount xs addr amt with
      | none => simp [hdebit'] at hdebit
      | some ys =>
        simp [hdebit'] at hdebit
        subst hdebit
        simp [noneg]
        exact ⟨hnonegx, xih ys hnonegxs hdebit'⟩
    
def creditAccount (ledger : Ledger) (addr : Addr) (amt : Amount) : Option Ledger :=
  match ledger with
  | []     => none
  | h :: t =>
    if (h.addr == addr)
    then some $ { h with bal := h.bal + amt } :: t
    else do
      let ledger' <- creditAccount t addr amt
      return (h :: ledger')

lemma creditAccount_adds_supply (ledger : Ledger) (addr : Addr) (amt : Amount) :
  ∀ ledger', ledger.creditAccount addr amt = some ledger'
  -> ledger'.getSupply = ledger.getSupply + amt := by sorry

def transferFunds (ledger : Ledger) (fromAddr toAddr : Addr) (amt : Amount) : Option Ledger := do
  let ledger' <- debitAccount ledger fromAddr amt
  creditAccount ledger' toAddr amt

theorem transferFunds_preserves_supply (ledger : Ledger) (fromAddr toAddr : Addr) (amt : Amount) :
  ∀ ledger', ledger.transferFunds fromAddr toAddr amt = some ledger'
  -> ledger'.getSupply = ledger.getSupply := by
  induction ledger with
  | nil => simp [transferFunds, debitAccount]
  | cons x xsl _ =>
    simp [transferFunds]
    cases hd : debitAccount (x :: xsl) fromAddr amt with
    | none => simp
    | some xsd =>
      simp
      cases hc : creditAccount xsd toAddr amt with
      | none => simp
      | some xsc =>
        simp
        have d := debitAccount_subtracts_supply (x :: xsl) fromAddr amt xsd
        have c := creditAccount_adds_supply xsd toAddr amt xsc
        rw [ c hc, d hd ]
        ring

lemma transferFunds_preserves_noneg (ledger : Ledger) (fromAddr toAddr : Addr) (amt : Amount) :
  ∀ ledger', ledger.noneg 
  -> ledger.transferFunds fromAddr toAddr amt = some ledger' 
  -> ledger'.noneg := by sorry

structure Proposal where
  id : Nat
  proposer : Addr
  amt : Amount
  yes : Nat
  no : Nat
  done : Bool
  deriving Repr

structure DAO where
  ledger : Ledger
  propl : List Proposal
  deriving Repr

namespace DAO

inductive Vote
  | yes
  | no
  deriving Repr

inductive Action
  | contrib (contributor : Addr) (amt : Amount)
  | propose (proposer : Addr) (amt : Amount)
  | vote (pid : Nat) (vote : Vote)
  | execute (pid : Nat)
  deriving Repr

def contrib (dao : DAO) (contributor : Addr) (amt : Amount) : Option DAO := do
  let ledger' <- dao.ledger.transferFunds contributor "treasury" amt
  return { dao with ledger := ledger' }

def propose (dao : DAO) (proposer : Addr) (amt : Amount) : Option DAO :=
  let prop := { id := dao.propl.length + 1, proposer, amt, yes := 0, no := 0, done := false }
  return { dao with propl := prop :: dao.propl }

def vote (dao : DAO) (pid : Nat) (v : Vote) : Option DAO :=
  let propl := dao.propl.map (fun p =>
      if p.id != pid
      then p
      else if p.done
      then p
      else
        match v with
        | .yes => { p with yes := p.yes + 1 }
        | .no  => { p with no  := p.no  + 1 })
  return { dao with propl := propl }

def execute (dao : DAO) (pid : Nat) : Option DAO := do
  let p <- dao.propl.find? (fun p => p.id == pid)
  if p.done
  then none
  else if p.yes <= p.no
  then none
  else do
    let l' <- dao.ledger.transferFunds "treasury" p.proposer p.amt
    return { dao with
      ledger := l'
      propl := dao.propl.map (fun q => if q.id == pid then { q with done := true } else q)
    }

def contract (dao : DAO) (act : Action) : Option DAO :=
  match act with
  | Action.contrib contributor amt  => dao.contrib contributor amt
  | Action.propose proposer amt     => dao.propose proposer amt
  | Action.vote pid vote            => dao.vote pid vote
  | Action.execute pid              => dao.execute pid

def genesis : DAO :=
  {
    ledger := [ { addr := "treasury", bal := 0 } ]
    propl := []
  }

def treasury (dao : DAO) : Option Amount := dao.ledger.getBalance "treasury"

def supply (dao : DAO) : Amount := dao.ledger.getSupply

lemma propose_never_fails (dao : DAO) (proposer : Addr) (amt : Amount) :
  ∃ dao', dao.contract (Action.propose proposer amt) = some dao' := ⟨_, rfl⟩

lemma vote_never_fails (dao : DAO) (pid : Nat) (v : Vote) :
  ∃ dao', dao.contract (Action.vote pid vt) = some dao' := ⟨_, rfl⟩

lemma propose_preserves_ledger (dao : DAO) (proposer : Addr) (amt : Amount) :
  ∀ dao', dao.contract (.propose proposer amt) = some dao' -> dao'.ledger = dao.ledger := by
  intro dao' h
  simp [contract, propose] at h
  subst h
  rfl

lemma vote_preserves_ledger (dao : DAO) (pid : Nat) (vt : Vote) :
  ∀ dao', dao.contract (.vote pid vt) = some dao' -> dao'.ledger = dao.ledger := by
  intro dao' h
  simp [contract, vote] at h
  subst h
  rfl

lemma contrib_preserves_propl (dao : DAO) (c : Addr) (amt : Amount) :
  ∀ dao', dao.contract (.contrib c amt) = some dao' -> dao'.propl = dao.propl := by
  intro dao' h
  simp [contract, contrib] at h
  cases ht : dao.ledger.transferFunds c "treasury" amt with
  | none    => simp [ht] at h
  | some l' =>
    simp [ht] at h
    subst h
    rfl

lemma propose_preserves_supply (dao : DAO) (proposer : Addr) (amt : Amount) :
  ∀ dao', dao.contract (.propose proposer amt) = some dao' -> dao'.supply = dao.supply := by
  intro dao' h
  unfold supply
  rw [propose_preserves_ledger dao proposer amt dao' h]

lemma vote_preserves_supply (dao : DAO) (pid : Nat) (vt : Vote) :
  ∀ dao', dao.contract (.vote pid vt) = some dao' -> dao'.supply = dao.supply := by
  intro dao' h
  unfold supply
  rw [vote_preserves_ledger dao pid vt dao' h]

lemma contrib_preserves_supply (dao : DAO) (c : Addr) (amt : Amount) :
  ∀ dao', dao.contract (.contrib c amt) = some dao' -> dao'.supply = dao.supply := by
  intro dao' h
  simp [contract, contrib] at h
  cases ht : dao.ledger.transferFunds c "treasury" amt with
  | none    => simp [ht] at h
  | some l' =>
    simp [ht] at h
    subst h
    simp [supply]
    exact transferFunds_preserves_supply dao.ledger c "treasury" amt l' ht

lemma execute_preserves_supply (dao : DAO) (pid : Nat) :
  ∀ dao', dao.contract (.execute pid) = some dao' -> dao'.supply = dao.supply := by
  intro dao' hexec
  simp [contract, execute] at hexec
  cases hfind : dao.propl.find? (fun p => p.id == pid) with
  | none => simp [hfind] at hexec
  | some p =>
    simp [hfind] at hexec
    obtain ⟨_, _, hbind⟩ := hexec
    cases ht : dao.ledger.transferFunds "treasury" p.proposer p.amt with
    | none => simp [ht] at hbind
    | some l' =>
      simp [ht, Option.bind] at hbind
      subst hbind
      simp [supply]
      exact transferFunds_preserves_supply dao.ledger "treasury" p.proposer p.amt l' ht

lemma contract_preserves_supply (dao : DAO) (act : Action) :
  ∀ dao', dao.contract act = some dao' -> dao'.supply = dao.supply := by
  intro dao' h
  cases act with
  | contrib con a  => simp only [contract] at h; exact contrib_preserves_supply  dao con a  dao' h
  | propose pro a  => simp only [contract] at h; exact propose_preserves_supply  dao pro a  dao' h
  | vote pid vt   => simp only [contract] at h; exact vote_preserves_supply      dao pid vt dao' h
  | execute pid  => simp only [contract] at h; exact execute_preserves_supply    dao pid    dao' h

lemma propose_increments_propl_count (dao : DAO) (proposer : Addr) (amt : Amount) :
  ∀ dao', dao.propose proposer amt = some dao'
  -> dao'.propl.length = dao.propl.length + 1 := by
  intro dao' h
  simp [propose] at h
  subst h
  simp

lemma vote_preserves_propl_count (dao : DAO) (pid : Nat) (v : Vote) :
  ∀ dao', dao.vote pid v = some dao'
  -> dao'.propl.length = dao.propl.length := by
  intro dao' h
  simp [vote] at h
  subst h
  simp

lemma execute_preserves_propl_count (dao : DAO) (pid : Nat) :
  ∀ dao', dao.execute pid = some dao'
  -> dao'.propl.length = dao.propl.length := by
  intro dao' hexec
  simp [execute] at hexec
  cases hfind : dao.propl.find? (fun p => p.id == pid) with
  | none => simp [hfind] at hexec
  | some p =>
    simp [hfind] at hexec
    obtain ⟨_, _, hbind⟩ := hexec
    cases ht : dao.ledger.transferFunds "treasury" p.proposer p.amt with
    | none => simp [ht] at hbind
    | some l' =>
      simp [ht, Option.bind] at hbind
      subst hbind
      simp

lemma execute_only_when_pass (dao : DAO) (pid : Nat) :
  ∀ dao', dao.execute pid = some dao' -> 
  ∃ p, dao.propl.find? (fun q => q.id == pid) = some p ∧ p.yes > p.no ∧ p.done = false := by
  intro dao' hexec
  simp [execute] at hexec
  cases hfind : dao.propl.find? (fun q => q.id == pid) with
  | none => simp [hfind] at hexec
  | some p =>
    simp [hfind] at hexec
    obtain ⟨hnot_done, hvote, _⟩ := hexec
    exact ⟨p, rfl, by omega, hnot_done⟩

theorem execute_preserves_noneg (dao : DAO) (pid : Nat) :
  ∀ dao', dao.ledger.noneg 
  -> dao.execute pid = some dao' 
  -> dao'.ledger.noneg := by
  intro dao' hnoneg hexec
  simp [execute] at hexec
  cases hfind : dao.propl.find? (fun q => q.id == pid) with
  | none => simp [hfind] at hexec
  | some p =>
    simp [hfind] at hexec
    obtain ⟨_, _, hbind⟩ := hexec
    cases ht : dao.ledger.transferFunds "treasury" p.proposer p.amt with
    | none => simp [ht] at hbind
    | some l' =>
      simp [ht, Option.bind] at hbind
      subst hbind
      exact transferFunds_preserves_noneg dao.ledger "treasury" p.proposer p.amt l' hnoneg ht

def run : DAO -> List Action -> Option DAO
  | dao, [] => some dao
  | dao, act :: acts => do
      let next ← dao.contract act
      run next acts

theorem run_preserves_supply (acts : List Action) (dao : DAO) :
  ∀ dao', run dao acts = some dao' → dao'.supply = dao.supply := by
  revert dao
  induction acts with
  | nil => 
    intro dao dao' h
    simp [run] at h
    subst h
    rfl
  | cons act acts ih =>
    intro dao dao' htrace
    simp [run] at htrace
    cases hstep : dao.contract act with
    | none => simp [hstep] at htrace
    | some next =>
      simp [hstep, Option.bind] at htrace
      have h_conserved := contract_preserves_supply dao act next hstep
      have h_future := ih next dao' htrace
      rw [h_future, h_conserved]

theorem supply_sound (acts : List Action) :
  ∀ dao', run genesis acts = some dao' → dao'.supply = genesis.supply := by
  intro dao' h
  exact run_preserves_supply acts genesis dao' h

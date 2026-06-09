import Mathlib.Data.List.Basic
import Mathlib.Tactic.SplitIfs
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
    let newTotalRaised := campaign.totalRaised + amt
    some {
      campaign := {
        campaign with
        backers := campaign.backers ++ [backer],
        totalRaised := newTotalRaised,
        funded := if newTotalRaised >= campaign.goal then true else false
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
      actor := { claimer with bal := claimer.bal + campaign.totalRaised },
      campaign := { campaign with funded := true, totalRaised := 0 }
    }

def claim (claimer : Account) (campaign : Campaign) (currentTime : Time) : Option ActionResult :=
  if currentTime <= campaign.maxTime then
    none
  else if campaign.backers.any (fun b => b.addr == claimer.addr) == False then
    none
  else if campaign.totalRaised >= campaign.goal then
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
        backers := campaign.backers.filter (fun b => b.addr != claimer.addr)
        totalRaised := campaign.totalRaised - amtDonatedByClaimer
      },
      actor := { claimer with bal := claimer.bal + amtDonatedByClaimer }
    }

-- Teorems --

--If claim returned some, then every condition is met
  theorem canClaimIfConditionsAreMet
  (claimer : Account)
  (campaign : Campaign)
  (currentTime : Time) :
  ∀ result, claim claimer campaign currentTime = some result ->
  currentTime > campaign.maxTime  ∧
  campaign.backers.any (fun b => b.addr == claimer.addr) ∧
  campaign.totalRaised < campaign.goal ∧
  !campaign.funded ∧
  campaign.backers.any (fun b => b.addr == claimer.addr) := by
  intro res result
  unfold claim at result
  repeat
    split at result
    · contradiction
  -- Because we added every negation of the if condition to the hypotesis, we now have every condition in goal under the hypotesis
  simp_all -- Simplifies using every hypotesis

theorem donate_increases_backers_length
    (donor : Account)
    (campaign : Campaign)
    (currentTime : Time)
    (amt : Amount) :
    ∀ result, donate donor campaign currentTime amt = some result
    -> result.campaign.backers.length = campaign.backers.length + 1 := by
  intro inv res
  unfold donate at res
  repeat
    split at res
    · contradiction
  cases res
  simp [List.length_append]

-- No se puede donar dos veces donate con persona es exitoso -> donate con la siguiente falla

-- totalRaised siempre es mayor o igual a cero (se podria probar para las tres)

-- Si currentBlock < maxBlock ∧ totalRaised > 0 → la longitud de backers es mayor a cero / Si se pudo hacer donate entonces la longitud de backers es mayor a cero

-- Si donate devuelve some, entonces result.campaign.funded = true ↔ campaign.totalRaised + amt >= campaign.goal

-- Si claim devuelve some, entonces el claimer ya no aparece en result.campaign.backers

-- Si claim devuelve some, entonces totalRaised baja en la cantidad igual que lo que dono

-- Si claim devuelve some, entonces la longitud de backers baja en 1

-- Si una cuenta no esta en backers, entonces claim devuelve none

-- donate preserva que no haya direcciones duplicadas en backers


theorem donate_preserves_no_duplicates
  (donor : Account)
  (campaign : Campaign)
  (currentTime : Time)
  (amt : Amount)
  (hNoDuplicates : ∀ backer, backer ∈ campaign.backers ->
    (campaign.backers.map Account.addr).count backer.addr = 1) :
  ∀ result, donate donor campaign currentTime amt = some result ->
    ∀ backer, backer ∈ result.campaign.backers ->
      (result.campaign.backers.map Account.addr).count backer.addr = 1 := by
        intro res d account hAccInBackers
        unfold donate at d
        split at d
        · contradiction
        rename_i hDonorNotInBackers
        repeat
          split at d
          · contradiction
        cases d -- Replaces res in goal with d

        have hDonorAddrCountZero : -- Donor isnt in backers before
            (campaign.backers.map Account.addr).count donor.addr = 0 := by
          rw [List.count_eq_zero]
          intro hMem
          apply hDonorNotInBackers
          simp at hMem
          rw [List.any_eq_true]
          rcases hMem with ⟨a, ha, hAddr⟩ -- Decomposes the hMem hypotesis intro three
          apply Exists.intro a
          constructor
          · exact ha
          · simp [hAddr]

        simp at hAccInBackers
        rcases hAccInBackers with hOld | hNew -- Decomposes the hAccInBackers in two cases
        -- In this case we have to prove that, assuming account was already a backer,
        -- adding the donor preserves the count of account.addr at exactly one.
        · have hAccountAddrNeDonor : account.addr ≠ donor.addr := by -- Donor account is different than account
            intro hEq -- Assume that is false to come to a contradiction
            have : donor.addr ∈ campaign.backers.map Account.addr := by
              rw [← hEq]
              exact List.mem_map_of_mem hOld -- If account is in backers, account.addr is in the transformed list backers.map Account.addr
            rw [List.count_eq_zero] at hDonorAddrCountZero
            exact hDonorAddrCountZero this -- Contradiction
          -- The old count is one by hNoDuplicates; the symmetric inequality lets simp prove
          -- that appending the donor does not add another occurrence of account.addr.
          simp [hNoDuplicates account hOld, Ne.symm hAccountAddrNeDonor]
        -- In this case we have to prove that, assuming account is the new donor,
        -- donor.addr appears exactly once after being added to the backers.
        · subst hNew -- Replaces account with the new donor backer, reducing account.addr to donor.addr
          simp [hDonorAddrCountZero] -- Uses that donor.addr previously appeared zero times to prove it now appears exactly once

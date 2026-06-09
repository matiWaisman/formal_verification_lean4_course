import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
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

-- Theorems --
-- Control flow property
theorem donate_cannot_donate_twice
    (donor : Account)
    (campaign : Campaign)
    (currentTime : Time)
    (amt : Amount) :
    ∀ result, donate donor campaign currentTime amt = some result ->
      ∀ currentTime' amt', donate donor result.campaign currentTime' amt' = none := by
      intro res hStep t' amt'

      have hDonorInList :
        res.campaign.backers.any (fun b => b.addr == donor.addr) := by
          -- We want to start seeing how res looks like.
          unfold donate at hStep
          -- We start splitting the ITE branches and discarding the ones that return none.
          split at hStep
          . contradiction -- if first guard is true, then: none = some res (contradiction)
          . repeat -- I couldve done the repeat at the beginning. But did one split just to show the if.
              split at hStep
              . contradiction
            -- Here we are left with the only branch that returned the new campaign.
            cases hStep -- We replace the res from hStep in the goal.
            simp [List.any_append]

      unfold donate -- We can use hDonorInList to prove the first condition of the if, and we get none=none.
      rw [if_pos hDonorInList] -- rw closes none=none automatically

-- Authorization property:
-- getFunds can only succeed if the one who does the action is the owner.
theorem getFunds_requires_owner
    (claimer : Account)
    (campaign : Campaign)
    (currentTime : Time) :
    ∀ result, getFunds claimer campaign currentTime = some result ->
      claimer.addr = campaign.owner.addr := by
      intro res hStep
      unfold getFunds at hStep
      -- We will see that, since the action succeeded, then
      -- none of the branch conditions that led to None were true.
      -- In particular, we want to obtain that (claimer.addr != campaign.owner.addr) does not hold.
      repeat
        split at hStep
        . contradiction
      rename_i periodEnded claimerIsOwner reachedGoal
      simp at claimerIsOwner
      blaster 

-- Very similar but for claim (using Blaster for the whole proof)
theorem claim_requires_backer
    (claimer : Account)
    (campaign : Campaign)
    (currentTime : Time) :
    ∀ result, claim claimer campaign currentTime = some result ->
      campaign.backers.any (fun b => b.addr == claimer.addr) := by
      blaster

-- If claim returns some, then all the required conditions are satisfied.
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

-- If donate returns some, then the backers length increases by one.
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

-- If someone claims, every backer with a different address remains unchanged in the list.
-- Since Account contains addr and bal, preserving the complete account also preserves its balance.
theorem claim_preserves_other_backers_membership
    (claimer : Account)
    (campaign : Campaign)
    (currentTime : Time) :
    ∀ result, claim claimer campaign currentTime = some result ->
      ∀ backer, backer ∈ campaign.backers ->
        backer.addr ≠ claimer.addr ->
          backer ∈ result.campaign.backers := by
  intro result hClaim backer hBackerInCampaign hBackerNeClaimer
  unfold claim at hClaim
  repeat
    split at hClaim
    . contradiction
  -- hClaim contains the result of claim in the some branch
  cases hClaim -- Replace result in goal with hClaim
  simp [hBackerInCampaign, hBackerNeClaimer]

-- If getFunds returns some, the new totalRaised is zero and therefore nonnegative.
theorem getFunds_sets_nonnegative_totalRaised
    (claimer : Account)
    (campaign : Campaign)
    (currentTime : Time) :
    ∀ result, getFunds claimer campaign currentTime = some result ->
      result.campaign.totalRaised >= 0 := by
    intro result hGetFunds
    unfold getFunds at hGetFunds
    repeat
      split at hGetFunds
      · contradiction
    cases hGetFunds
    simp


-- If every backer has a positive balance and claim returns some, totalRaised decreases.
theorem claim_decreases_totalRaised
    (claimer : Account)
    (campaign : Campaign)
    (currentTime : Time)
    (hBackersBalancePositive :
      ∀ account, account ∈ campaign.backers -> account.bal > 0) :
    ∀ result, claim claimer campaign currentTime = some result →
      result.campaign.totalRaised < campaign.totalRaised := by
    intro actionResult hClaim
    unfold claim at hClaim

    repeat
      split at hClaim
      . contradiction

    cases hClaim
    simp

    have hAny :
    campaign.backers.any (fun backer => backer.addr == claimer.addr) = true := by
      simp_all

    sorry

-- If a donation succeeds, a second donation from the same account fails.
theorem cannot_donate_twice
    (donor : Account)
    (campaign : Campaign)
    (currentTime : Time)
    (amt : Amount) :
    ∀ result, donate donor campaign currentTime amt = some result ->
      donate donor result.campaign currentTime amt = none := by
  sorry

-- If totalRaised was nonnegative and donate returns some, the new totalRaised remains nonnegative.
theorem donate_preserves_nonnegative_totalRaised
    (donor : Account)
    (campaign : Campaign)
    (currentTime : Time)
    (amt : Amount)
    (hTotalRaisedNonnegative : campaign.totalRaised >= 0) :
    ∀ result, donate donor campaign currentTime amt = some result ->
      result.campaign.totalRaised >= 0 := by
  sorry

-- If every backer donated at most totalRaised and claim returns some, the new totalRaised is nonnegative.
theorem claim_preserves_nonnegative_totalRaised
    (claimer : Account)
    (campaign : Campaign)
    (currentTime : Time)
    (hBackersCovered :
      ∀ backer, backer ∈ campaign.backers -> backer.bal <= campaign.totalRaised) :
    ∀ result, claim claimer campaign currentTime = some result ->
      result.campaign.totalRaised >= 0 := by
  sorry

-- If donate returns some, then the resulting backers list is not empty.
theorem donate_success_implies_nonempty_backers
    (donor : Account)
    (campaign : Campaign)
    (currentTime : Time)
    (amt : Amount) :
    ∀ result, donate donor campaign currentTime amt = some result ->
      result.campaign.backers.length > 0 := by
  intro result hDonate
  have hLength :=
    donate_increases_backers_length donor campaign currentTime amt result hDonate
  clear hDonate donor currentTime amt
  omega

-- If there were no duplicate addresses before claim, there are none afterward.
theorem claim_preserves_no_duplicates
    (claimer : Account)
    (campaign : Campaign)
    (currentTime : Time)
    (hNoDuplicates : ∀ backer, backer ∈ campaign.backers ->
      (campaign.backers.map Account.addr).count backer.addr = 1) :
    ∀ result, claim claimer campaign currentTime = some result ->
      ∀ backer, backer ∈ result.campaign.backers ->
        (result.campaign.backers.map Account.addr).count backer.addr = 1 := by
  intro res hClaim hAccount hAccountInRes
  unfold claim at hClaim

  repeat
    split at hClaim
    . contradiction

  cases hClaim
  have hAccountInOriginal : hAccount ∈ campaign.backers := by
    simp at hAccountInRes
    exact hAccountInRes.1

  have hOriginalNodup : (campaign.backers.map Account.addr).Nodup := by
    rw [List.nodup_iff_count_eq_one]
    intro addr hAddrInMap
    simp at hAddrInMap
    rcases hAddrInMap with ⟨backer, hBackerMem, hAddrEq⟩
    rw [← hAddrEq]
    exact hNoDuplicates backer hBackerMem

  have hResultNodup :
      ((campaign.backers.filter fun backer => backer.addr != claimer.addr).map Account.addr).Nodup :=
    hOriginalNodup.sublist (List.filter_sublist.map Account.addr)
  exact List.count_eq_one_of_mem hResultNodup (List.mem_map_of_mem hAccountInRes)

-- If there were no duplicate addresses before donate, there are none afterward.
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



-- If donate returns some, funded is true exactly when the new total reaches the goal.
theorem donate_sets_funded_iff_goal_reached
    (donor : Account)
    (campaign : Campaign)
    (currentTime : Time)
    (amt : Amount) :
    ∀ result, donate donor campaign currentTime amt = some result ->
      (result.campaign.funded = true ↔ campaign.totalRaised + amt >= campaign.goal) := by
  sorry

-- If claim returns some, no resulting backer has the claimer's address.
theorem claim_removes_claimer
    (claimer : Account)
    (campaign : Campaign)
    (currentTime : Time) :
    ∀ result, claim claimer campaign currentTime = some result ->
      ∀ backer, backer ∈ result.campaign.backers ->
        backer.addr ≠ claimer.addr := by
  sorry

-- If there were no duplicate addresses and claim returns some, the backers length decreases by one.
theorem claim_decreases_backers_length_by_one
    (claimer : Account)
    (campaign : Campaign)
    (currentTime : Time)
    (hNoDuplicates : (campaign.backers.map Account.addr).Nodup) :
    ∀ result, claim claimer campaign currentTime = some result ->
      result.campaign.backers.length + 1 = campaign.backers.length := by
  sorry

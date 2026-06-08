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
    some {
      campaign := {
        campaign with
        backers := campaign.backers ++ [backer],
        totalRaised := campaign.totalRaised + amt
      },
      actor := { donor with bal := donor.bal - amt }
    }


def getFunds (claimer : Account) (campaign : Campaign) (currentTime : Time) : Option ActionResult :=
  if currentTime <= campaign.maxTime then
    none
  else if claimer.addr != campaign.owner.addr then
    none
  else if campaign.totalRaised <= campaign.goal then
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
      },
      actor := { claimer with bal := claimer.bal + amtDonatedByClaimer }
    }

-- Si claim devolvio some, entonces el currentBlock es mayor a max block y se cumplen el resto de las condiciones
/-
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

-/


-- No se puede donar dos veces donate con persona es exitoso -> donate con la siguiente falla

-- totalRaised siempre es mayor o igual a cero (se podria probar para las tres)

-- Si currentBlock < maxBlock ∧ totalRaised > 0 → la longitud de backers es mayor a cero / Si se pudo hacer donate entonces la longitud de backers es mayor a cero




theorem donate_preserves_backersCount_invariant
    (donor : Account)
    (campaign : Campaign)
    (currentTime : Time)
    (amt : Amount) :
    ∀ result, donate donor campaign currentTime amt = some result
    -> result.campaign.backers.length = campaign.backers.length + 1 := by
  intro inv res
  unfold donate at res
  split at res
  · contradiction
  . split at res
    . contradiction
    . split at res
      . contradiction
      . split at res
        . contradiction
        . split at res
          . contradiction
          . cases res
            simp [List.length_append]


/-
theorem claim_preserves_backersCount_invariant
    (claimer : Account)
    (campaign : Campaign)
    (currentTime : Time) :
    campaign.backersCount = campaign.backers.length
    -> backersNoDuplicateAddresses campaign.backers
    -> ∀ result, claim claimer campaign currentTime = some result
    -> result.campaign.backersCount = result.campaign.backers.length := by
  intro inv nodup result res
  unfold claim at res
  repeat
    split at res
    · contradiction
-/

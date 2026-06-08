use aiken/collection/list
use aiken/crypto.{VerificationKeyHash}
use aiken/interval
use cardano/address
use cardano/assets
use cardano/script_context.{ScriptContext}
use cardano/transaction.{Input, Output, OutputReference, Transaction}

pub type Contribution {
  contributor: VerificationKeyHash,
  amount: Int,
}

pub type CampaignDatum {
  owner: VerificationKeyHash,
  deadline: Int,
  goal: Int,
  funded: Bool,
  total_raised: Int,
  contributions: List<Contribution>,
  backers_count: Int,
}

pub type CampaignRedeemer {
  Donate { donor: VerificationKeyHash, amount: Int, next_datum: CampaignDatum }
  GetFunds
  Claim { claimant: VerificationKeyHash, next_datum: Option<CampaignDatum> }
}

fn signed_by(tx: Transaction, signer: VerificationKeyHash) -> Bool {
  list.has(tx.extra_signatories, signer)
}

fn before_deadline(tx: Transaction, deadline: Int) -> Bool {
  interval.is_entirely_before(tx.validity_range, deadline)
}

fn after_deadline(tx: Transaction, deadline: Int) -> Bool {
  interval.is_entirely_after(tx.validity_range, deadline)
}

fn lovelace_in(output: Output) -> Int {
  assets.lovelace_of(output.value)
}

fn own_output(tx: Transaction, own_ref: OutputReference) -> Output {
  find_output(tx.inputs, own_ref)
}

fn find_output(inputs: List<Input>, own_ref: OutputReference) -> Output {
  when inputs is {
    [] -> fail
    [Input { output_reference, output }, ..rest] ->
      if output_reference == own_ref {
        output
      } else {
        find_output(rest, own_ref)
      }
  }
}

fn own_script_outputs(tx: Transaction, own_ref: OutputReference) -> List<Output> {
  let input = own_output(tx, own_ref)
  list.filter(tx.outputs, fn(output) { output.address == input.address })
}

fn own_continuing_output(tx: Transaction, own_ref: OutputReference) -> Output {
  expect [output] = own_script_outputs(tx, own_ref)
  output
}

fn contribution_of(
  contributions: List<Contribution>,
  contributor: VerificationKeyHash,
) -> Option<Contribution> {
  list.find(
    contributions,
    fn(contribution) { contribution.contributor == contributor },
  )
}

fn has_contributed(
  contributions: List<Contribution>,
  contributor: VerificationKeyHash,
) -> Bool {
  when contribution_of(contributions, contributor) is {
    Some(_) -> True
    None -> False
  }
}

fn remove_contribution(
  contributions: List<Contribution>,
  contributor: VerificationKeyHash,
) -> List<Contribution> {
  list.filter(
    contributions,
    fn(contribution) { contribution.contributor != contributor },
  )
}

fn sum_contributions(contributions: List<Contribution>) -> Int {
  list.foldl(
    contributions,
    0,
    fn(contribution, total) { total + contribution.amount },
  )
}

fn every_contribution_is_positive(contributions: List<Contribution>) -> Bool {
  list.all(contributions, fn(contribution) { contribution.amount > 0 })
}

fn no_duplicate_contributors(contributions: List<Contribution>) -> Bool {
  list.length(contributions) == list.length(
    list.unique(
      list.map(contributions, fn(contribution) { contribution.contributor }),
    ),
  )
}

fn datum_invariants(datum: CampaignDatum) -> Bool {
  and {
    datum.goal > 0,
    datum.total_raised >= 0,
    datum.backers_count == list.length(datum.contributions),
    datum.total_raised == sum_contributions(datum.contributions),
    every_contribution_is_positive(datum.contributions),
    no_duplicate_contributors(datum.contributions),
  }
}

fn keeps_campaign_config(old: CampaignDatum, new: CampaignDatum) -> Bool {
  and {
    new.owner == old.owner,
    new.deadline == old.deadline,
    new.goal == old.goal,
    new.funded == old.funded,
  }
}

fn donate(
  datum: CampaignDatum,
  donor: VerificationKeyHash,
  amount: Int,
  next_datum: CampaignDatum,
  own_ref: OutputReference,
  tx: Transaction,
) -> Bool {
  let input = own_output(tx, own_ref)
  let output = own_continuing_output(tx, own_ref)

  let previous_lovelace = lovelace_in(input)
  let next_lovelace = lovelace_in(output)
  let expected_contribution = Contribution { contributor: donor, amount }

  and {
    datum_invariants(datum),
    before_deadline(tx, datum.deadline),
    signed_by(tx, donor),
    amount > 0,
    !has_contributed(datum.contributions, donor),
    keeps_campaign_config(datum, next_datum),
    next_datum.total_raised == datum.total_raised + amount,
    next_datum.contributions == list.concat(
      datum.contributions,
      [expected_contribution],
    ),
    next_datum.backers_count == datum.backers_count + 1,
    next_lovelace == previous_lovelace + amount,
    datum_invariants(next_datum),
  }
}

fn get_funds(
  datum: CampaignDatum,
  own_ref: OutputReference,
  tx: Transaction,
) -> Bool {
  let input = own_output(tx, own_ref)
  let owner_address = address.from_verification_key(datum.owner)
  let owner_is_paid =
    list.any(
      tx.outputs,
      fn(output) {
        and {
          output.address == owner_address,
          lovelace_in(output) >= lovelace_in(input),
        }
      },
    )

  and {
    datum_invariants(datum),
    after_deadline(tx, datum.deadline),
    signed_by(tx, datum.owner),
    !datum.funded,
    datum.total_raised >= datum.goal,
    owner_is_paid,
    list.is_empty(own_script_outputs(tx, own_ref)),
  }
}

fn claim(
  datum: CampaignDatum,
  claimant: VerificationKeyHash,
  next_datum: Option<CampaignDatum>,
  own_ref: OutputReference,
  tx: Transaction,
) -> Bool {
  expect Some(contribution) = contribution_of(datum.contributions, claimant)

  let input = own_output(tx, own_ref)
  let refund_amount = contribution.amount
  let remaining_contributions =
    remove_contribution(datum.contributions, claimant)
  let claimant_address = address.from_verification_key(claimant)
  let claimant_is_paid =
    list.any(
      tx.outputs,
      fn(output) {
        and {
          output.address == claimant_address,
          lovelace_in(output) >= refund_amount,
        }
      },
    )

  let continuing_outputs = own_script_outputs(tx, own_ref)
  let state_is_updated =
    when next_datum is {
      None -> and {
          list.is_empty(continuing_outputs),
          list.is_empty(remaining_contributions),
        }
      Some(next_datum) ->
        when continuing_outputs is {
          [output] -> and {
              keeps_campaign_config(datum, next_datum),
              next_datum.total_raised == datum.total_raised - refund_amount,
              next_datum.contributions == remaining_contributions,
              next_datum.backers_count == datum.backers_count - 1,
              lovelace_in(output) == lovelace_in(input) - refund_amount,
              datum_invariants(next_datum),
            }
          _ -> False
        }
    }

  and {
    datum_invariants(datum),
    after_deadline(tx, datum.deadline),
    signed_by(tx, claimant),
    !datum.funded,
    datum.total_raised < datum.goal,
    refund_amount > 0,
    claimant_is_paid,
    state_is_updated,
  }
}

validator crowfunding {
  spend(
    datum: Option<CampaignDatum>,
    redeemer: CampaignRedeemer,
    own_ref: OutputReference,
    tx: Transaction,
  ) {
    expect Some(campaign) = datum

    when redeemer is {
      Donate { donor, amount, next_datum } ->
        donate(campaign, donor, amount, next_datum, own_ref, tx)
      GetFunds -> get_funds(campaign, own_ref, tx)
      Claim { claimant, next_datum } ->
        claim(campaign, claimant, next_datum, own_ref, tx)
    }
  }

  else(_ctx: ScriptContext) {
    False
  }
}

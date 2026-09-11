/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.CompoundChannel
import CapacityAtlasForMathlib.InformationTheory.ChannelMixture

open scoped BigOperators
open CapacityAtlas
open CapacityAtlas.CompoundChannel

namespace CapacityAtlasCompound

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S] [Nonempty S]

/-- Average information-density variance across the channel family. -/
noncomputable def averageInformationVariance (channels : S → FiniteChannel X Y)
    (input : FiniteDistribution X) : ℝ :=
  (Fintype.card S : ℝ)⁻¹ * ∑ s, (channels s).informationVariance input

theorem averageInformationVariance_nonnegative (channels : S → FiniteChannel X Y)
    (input : FiniteDistribution X) : 0 ≤ averageInformationVariance channels input := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun s _ ↦ (channels s).informationVariance_nonnegative input

/-- One deterministic encoder and decoder work simultaneously for every fixed member. -/
theorem exists_blockCode_uniform_error_le
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X)
    (a δ : ℝ) (ha : ∀ s, a ≤ (channels s).mutualInformation input)
    {n messages : ℕ} (hn : 0 < n) (hmessages : 0 < messages) (hδ : 0 < δ) :
    ∃ code : CompoundChannel.BlockCode X Y n,
      code.messageCount = messages ∧
        ∀ s, code.averageErrorProbability (channels s) ≤
          (Fintype.card S : ℝ) *
            (((n : ℝ) * averageInformationVariance channels input) / (((n : ℝ) * δ) ^ 2) +
              Real.exp (-((n : ℝ) * δ)) +
              (messages : ℝ) * Real.exp
                (-((n : ℝ) * a - 2 * (n : ℝ) * δ - Real.log (Fintype.card S)))) := by
  letI : Nonempty (Fin messages) := Fin.pos_iff_nonempty.mp hmessages
  let blocks : S → FiniteChannel (Fin n → X) (Fin n → Y) := fun s ↦ (channels s).block n
  let reference := FiniteChannel.mixture (FiniteDistribution.uniform S) blocks
  let threshold := (n : ℝ) * a - 2 * (n : ℝ) * δ - Real.log (Fintype.card S)
  let variance := averageInformationVariance channels input
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcomponent (s : S) :
      (blocks s).informationDensityLowerTailMass (input.iid n)
          (threshold + Real.log (Fintype.card S) + (n : ℝ) * δ) ≤
        ((n : ℝ) * (channels s).informationVariance input) / (((n : ℝ) * δ) ^ 2) := by
    calc
      _ ≤ (blocks s).informationDensityLowerTailMass (input.iid n)
          ((n : ℝ) * (channels s).mutualInformation input - (n : ℝ) * δ) := by
        apply FiniteChannel.informationDensityLowerTailMass_mono
        dsimp [threshold]
        nlinarith [mul_le_mul_of_nonneg_left (ha s) hnReal.le]
      _ ≤ _ := by
        rw [FiniteChannel.block_informationDensityLowerTailMass_eq]
        exact (channels s).blockInformationDensity_lowerTail_le input hn hδ
  have htail : reference.informationDensityLowerTailMass (input.iid n) threshold ≤
      ((n : ℝ) * variance) / (((n : ℝ) * δ) ^ 2) + Real.exp (-((n : ℝ) * δ)) := by
    calc
      _ ≤ (Fintype.card S : ℝ)⁻¹ *
          ∑ s, (blocks s).informationDensityLowerTailMass (input.iid n)
            (threshold + Real.log (Fintype.card S) + (n : ℝ) * δ) +
          Real.exp (-((n : ℝ) * δ)) :=
        FiniteChannel.uniformMixture_informationDensityLowerTailMass_le
          blocks (input.iid n) threshold ((n : ℝ) * δ)
      _ ≤ (Fintype.card S : ℝ)⁻¹ *
          ∑ s, ((n : ℝ) * (channels s).informationVariance input) /
            (((n : ℝ) * δ) ^ 2) + Real.exp (-((n : ℝ) * δ)) := by
        apply add_le_add_left
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun s _ ↦ hcomponent s) (by positivity)
      _ = _ := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
        dsimp [variance, averageInformationVariance]
        ring
  obtain ⟨oneShot, honeShot⟩ :=
    reference.exists_oneShotCode_averageErrorProbability_le
      (input.iid n) threshold (M := Fin messages)
  let code : CompoundChannel.BlockCode X Y n :=
    { messageCount := messages
      messageCount_pos := hmessages
      encode := oneShot.encode
      decode := oneShot.decode }
  refine ⟨code, rfl, ?_⟩
  intro s
  have hstate := oneShot.averageErrorProbability_le_card_mul_uniformMixture blocks s
  change (oneShot.onChannel (blocks s)).averageErrorProbability ≤
    (Fintype.card S : ℝ) * (oneShot.onChannel reference).averageErrorProbability at hstate
  rw [OneShotCode.onChannel_self] at hstate
  have hconversion : code.averageErrorProbability (channels s) =
      (oneShot.onChannel (blocks s)).averageErrorProbability := rfl
  have hstate' : code.averageErrorProbability (channels s) ≤
      (Fintype.card S : ℝ) * oneShot.averageErrorProbability := by
    rw [hconversion]
    exact hstate
  apply hstate'.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Fintype.card_fin] using honeShot.trans (add_le_add_left htail _)

private theorem compoundBound_tendsto_zero (variance δ k : ℝ) (hδ : 0 < δ) :
    Filter.Tendsto
      (fun n : ℕ ↦ k * (((n : ℝ) * variance) / (((n : ℝ) * δ) ^ 2) +
        (1 + 2 * k) * Real.exp (-((n : ℝ) * δ))))
      Filter.atTop (nhds 0) := by
  have hfirstBase : Filter.Tendsto
      (fun n : ℕ ↦ (variance / δ ^ 2) / (n : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.const_div_atTop (variance / δ ^ 2)
  have hfirst : Filter.Tendsto
      (fun n : ℕ ↦ ((n : ℝ) * variance) / (((n : ℝ) * δ) ^ 2))
      Filter.atTop (nhds 0) := by
    apply hfirstBase.congr'
    filter_upwards [Filter.eventually_ne_atTop 0] with n hn
    have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp [hnReal, hδ.ne']
  have hscaled : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * δ) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hδ
  have hexponential : Filter.Tendsto
      (fun n : ℕ ↦ Real.exp (-((n : ℝ) * δ))) Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp
      ((Filter.tendsto_neg_atTop_atBot : Filter.Tendsto (fun x : ℝ ↦ -x)
        Filter.atTop Filter.atBot).comp hscaled)
  simpa using (hfirst.add (hexponential.const_mul (1 + 2 * k))).const_mul k

/-- Every nonnegative rate below a fixed input's least mutual information is achievable
with one decoder independent of the unknown channel member. -/
theorem achievableRate_of_lt_worstInformationBits
    (channels : S → FiniteChannel X Y) (input : FiniteDistribution X)
    {rate : ℝ} (hnonnegative : 0 ≤ rate)
    (hrate : rate < worstInformationBits channels input) :
    CompoundChannel.AchievableRate channels rate := by
  let a := worstInformationBits channels input * Real.log 2
  let δ := (a - rate * Real.log 2) / 3
  let k : ℝ := Fintype.card S
  let variance := averageInformationVariance channels input
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hδ : 0 < δ := by
    dsimp [δ, a]
    nlinarith [mul_lt_mul_of_pos_right hrate hlogTwo]
  have hk : 0 < k := by dsimp [k]; exact_mod_cast Fintype.card_pos
  have ha (s : S) : a ≤ (channels s).mutualInformation input := by
    have h := worstInformationBits_le channels input s
    exact (le_div_iff₀ hlogTwo).mp h
  intro ε hε
  have hlimit := compoundBound_tendsto_zero variance δ k hδ
  have heventually : ∀ᶠ n : ℕ in Filter.atTop,
      k * (((n : ℝ) * variance) / (((n : ℝ) * δ) ^ 2) +
        (1 + 2 * k) * Real.exp (-((n : ℝ) * δ))) < ε :=
    (tendsto_order.1 hlimit).2 ε hε
  obtain ⟨first, hfirst⟩ := Filter.eventually_atTop.1 heventually
  refine ⟨max 1 first, by omega, ?_⟩
  intro n hn
  have hnPos : 0 < n := by omega
  let messages := FiniteChannel.messageCountAtRate rate n
  have hmessages : 0 < messages := FiniteChannel.messageCountAtRate_pos rate n
  obtain ⟨code, hcount, herror⟩ :=
    exists_blockCode_uniform_error_le channels input a δ ha hnPos hmessages hδ
  refine ⟨code, ?_, ?_⟩
  · have hmessageUpper : (messages : ℝ) ≤
        2 * Real.exp ((n : ℝ) * rate * Real.log 2) := by
      exact FiniteChannel.natCeil_exp_le_two_mul_exp (by positivity)
    have hexponential :
        (messages : ℝ) * Real.exp (-((n : ℝ) * a - 2 * (n : ℝ) * δ - Real.log k)) ≤
          2 * k * Real.exp (-((n : ℝ) * δ)) := by
      calc
        _ ≤ (2 * Real.exp ((n : ℝ) * rate * Real.log 2)) *
            Real.exp (-((n : ℝ) * a - 2 * (n : ℝ) * δ - Real.log k)) :=
          mul_le_mul_of_nonneg_right hmessageUpper (Real.exp_pos _).le
        _ = 2 * Real.exp (-((n : ℝ) * δ) + Real.log k) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          dsimp [δ]
          ring
        _ = 2 * k * Real.exp (-((n : ℝ) * δ)) := by
          rw [Real.exp_add, Real.exp_log hk]
          ring
    intro s
    calc
      code.averageErrorProbability (channels s) ≤
          k * (((n : ℝ) * variance) / (((n : ℝ) * δ) ^ 2) +
            Real.exp (-((n : ℝ) * δ)) +
            (messages : ℝ) * Real.exp
              (-((n : ℝ) * a - 2 * (n : ℝ) * δ - Real.log k))) := herror s
      _ ≤ k * (((n : ℝ) * variance) / (((n : ℝ) * δ) ^ 2) +
          Real.exp (-((n : ℝ) * δ)) + 2 * k * Real.exp (-((n : ℝ) * δ))) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hexponential _) hk.le
      _ = k * (((n : ℝ) * variance) / (((n : ℝ) * δ) ^ 2) +
          (1 + 2 * k) * Real.exp (-((n : ℝ) * δ))) := by ring
      _ ≤ ε := (hfirst n (by omega)).le
  · rw [CompoundChannel.BlockCode.rate, hcount]
    exact FiniteChannel.targetRate_le_rateOfMessageCountAtRate rate hnPos

/-- Maximizing the common input law gives direct coding below compound information capacity. -/
theorem achievableRate_of_lt_informationCapacityBits [Nonempty X]
    (channels : S → FiniteChannel X Y) {rate : ℝ} (hnonnegative : 0 ≤ rate)
    (hrate : rate < CompoundChannel.informationCapacityBits channels) :
    CompoundChannel.AchievableRate channels rate := by
  obtain ⟨input, hinput⟩ := exists_capacityAchieving_input channels
  exact achievableRate_of_lt_worstInformationBits channels input hnonnegative
    (by simpa [hinput] using hrate)

end CapacityAtlasCompound

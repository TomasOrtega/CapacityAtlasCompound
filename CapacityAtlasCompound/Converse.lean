/-
Copyright 2026 The Capacity Atlas Authors
Licensed under the Apache License, Version 2.0 (the "License").
See the License for the specific language governing permissions and limitations.
-/

import CapacityAtlasForMathlib.InformationTheory.CompoundChannel
import CapacityAtlasForMathlib.InformationTheory.BlockInputInformation
import CapacityAtlasForMathlib.InformationTheory.CodingConverse

open scoped BigOperators
open CapacityAtlas

namespace CapacityAtlasCompound

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]

/-- The encoder's word distribution is independent of the channel member. -/
noncomputable def blockCodeInputDistribution {n : ℕ}
    (code : CompoundChannel.BlockCode X Y n) : FiniteDistribution (Fin n → X) := by
  classical
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  exact (FiniteDistribution.uniform (Fin code.messageCount)).map code.encode

/-- Uniform averaging of the same input marginals for every channel member. -/
noncomputable def blockCodeAverageInput {n : ℕ}
    (code : CompoundChannel.BlockCode X Y n) (hn : 0 < n) : FiniteDistribution X := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact (blockCodeInputDistribution code).averageCoordinateMarginal

/-- Fano's inequality retains the common averaged input distribution. -/
theorem blockCode_log_messageCount_le (channel : FiniteChannel X Y) {n : ℕ}
    (code : CompoundChannel.BlockCode X Y n) (hn : 0 < n) :
    Real.log code.messageCount ≤
      (n : ℝ) * channel.mutualInformation (blockCodeAverageInput code hn) + Real.log 2 +
        code.averageErrorProbability channel * Real.log code.messageCount := by
  classical
  letI : Nonempty (Fin code.messageCount) := Fin.pos_iff_nonempty.mp code.messageCount_pos
  letI : NeZero n := ⟨hn.ne'⟩
  have hfano := ((channel.block n).encoded code.encode).fano_uniform code.decode
  simp only [Fintype.card_fin] at hfano
  change Real.log code.messageCount ≤
    ((channel.block n).encoded code.encode).mutualInformation
      (FiniteDistribution.uniform (Fin code.messageCount)) + Real.log 2 +
        code.averageErrorProbability channel * Real.log code.messageCount at hfano
  rw [FiniteChannel.encoded_mutualInformation] at hfano
  have hmutual :=
    channel.block_mutualInformation_le_mul_averageCoordinateMarginal
      (blockCodeInputDistribution code)
  change (channel.block n).mutualInformation
      ((FiniteDistribution.uniform (Fin code.messageCount)).map code.encode) ≤
    (n : ℝ) * channel.mutualInformation (blockCodeAverageInput code hn) at hmutual
  linarith

/-- A statewise rate bound with an input law shared by the whole family. -/
theorem blockCode_rate_bound (channel : FiniteChannel X Y) {n : ℕ}
    (code : CompoundChannel.BlockCode X Y n) (hn : 0 < n) :
    (1 - code.averageErrorProbability channel) * code.rate ≤
      channel.mutualInformationBits (blockCodeAverageInput code hn) + (n : ℝ)⁻¹ := by
  have hlogBound := blockCode_log_messageCount_le channel code hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrearranged :
      (1 - code.averageErrorProbability channel) * Real.log code.messageCount ≤
        (n : ℝ) * channel.mutualInformation (blockCodeAverageInput code hn) + Real.log 2 := by
    linarith
  unfold CompoundChannel.BlockCode.rate Real.logb FiniteChannel.mutualInformationBits
  calc
    (1 - code.averageErrorProbability channel) *
        (Real.log code.messageCount / Real.log 2 / (n : ℝ)) =
        ((1 - code.averageErrorProbability channel) * Real.log code.messageCount) /
          ((n : ℝ) * Real.log 2) := by
      field_simp [hnReal.ne', hlogTwo.ne']
    _ ≤ ((n : ℝ) * channel.mutualInformation (blockCodeAverageInput code hn) +
          Real.log 2) / ((n : ℝ) * Real.log 2) :=
      div_le_div_of_nonneg_right hrearranged (mul_pos hnReal hlogTwo).le
    _ = channel.mutualInformation (blockCodeAverageInput code hn) / Real.log 2 +
        (n : ℝ)⁻¹ := by
      field_simp [hnReal.ne', hlogTwo.ne']

/-- Uniform reliability allows minimization over the family with the same input law. -/
theorem blockCode_uniform_rate_bound [Nonempty S]
    (channels : S → FiniteChannel X Y) {n : ℕ}
    (code : CompoundChannel.BlockCode X Y n) (hn : 0 < n)
    {rate ε : ℝ} (hrate : 0 ≤ rate) (hε : ε < 1)
    (herror : ∀ s, code.averageErrorProbability (channels s) ≤ ε)
    (hcodeRate : rate ≤ code.rate) :
    (1 - ε) * rate ≤ CompoundChannel.informationCapacityBits channels + (n : ℝ)⁻¹ := by
  have hcommon : (1 - ε) * rate - (n : ℝ)⁻¹ ≤
      CompoundChannel.worstInformationBits channels (blockCodeAverageInput code hn) := by
    apply CompoundChannel.le_worstInformationBits
    intro s
    have hfactorNonnegative : 0 ≤ 1 - code.averageErrorProbability (channels s) := by
      have := herror s
      linarith
    have hlower :
        (1 - ε) * rate ≤ (1 - code.averageErrorProbability (channels s)) * code.rate := by
      calc
        (1 - ε) * rate ≤ (1 - code.averageErrorProbability (channels s)) * rate :=
          mul_le_mul_of_nonneg_right (sub_le_sub_left (herror s) 1) hrate
        _ ≤ (1 - code.averageErrorProbability (channels s)) * code.rate :=
          mul_le_mul_of_nonneg_left hcodeRate hfactorNonnegative
    have hupper := blockCode_rate_bound (channels s) code hn
    linarith
  have hcapacity :=
    CompoundChannel.worstInformationBits_le_informationCapacityBits channels
      (blockCodeAverageInput code hn)
  linarith

/-- No uniformly achievable rate exceeds the max–min information target. -/
theorem achievableRate_le_informationCapacityBits [Nonempty S] [Nonempty X]
    (channels : S → FiniteChannel X Y) {rate : ℝ}
    (hachievable : CompoundChannel.AchievableRate channels rate) :
    rate ≤ CompoundChannel.informationCapacityBits channels := by
  let capacity := CompoundChannel.informationCapacityBits channels
  by_contra hrateCapacity
  have hstrict : capacity < rate := lt_of_not_ge hrateCapacity
  have hcapacityNonnegative : 0 ≤ capacity :=
    CompoundChannel.informationCapacityBits_nonnegative channels
  have hratePositive : 0 < rate := lt_of_le_of_lt hcapacityNonnegative hstrict
  let gap := rate - capacity
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hgapRate : gap ≤ rate := by dsimp [gap]; linarith
  let ε := gap / (4 * rate)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεlt : ε < 1 := by
    apply (div_lt_one (mul_pos (by norm_num) hratePositive)).2
    linarith
  have hεRate : ε * rate = gap / 4 := by
    dsimp [ε]
    field_simp [hratePositive.ne']
  obtain ⟨firstBlocklength, hfirstPositive, hcodes⟩ := hachievable ε hε
  obtain ⟨n, hnLarge⟩ := exists_nat_gt (max (firstBlocklength : ℝ) (4 / gap))
  have hfirstBlocklength : firstBlocklength ≤ n := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hnLarge).le
  have hnPositive : 0 < n := lt_of_lt_of_le hfirstPositive hfirstBlocklength
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hnPositive
  have hfourDiv : 4 / gap < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hnLarge
  have hfourProduct : 4 < (n : ℝ) * gap := (div_lt_iff₀ hgap).mp hfourDiv
  have hinversePositive : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnReal
  have hinverseProduct : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnReal.ne'
  have hinverseSmall : (n : ℝ)⁻¹ < gap / 4 := by nlinarith
  obtain ⟨code, herror, hcodeRate⟩ := hcodes n hfirstBlocklength
  have hcombined := blockCode_uniform_rate_bound channels code hnPositive
    hratePositive.le hεlt herror hcodeRate
  change (1 - ε) * rate ≤ capacity + (n : ℝ)⁻¹ at hcombined
  dsimp [gap] at hgap hεRate hinverseSmall
  nlinarith

theorem achievableRates_bddAbove [Nonempty S] [Nonempty X]
    (channels : S → FiniteChannel X Y) :
    BddAbove {rate | rate = 0 ∨ CompoundChannel.AchievableRate channels rate} := by
  refine ⟨CompoundChannel.informationCapacityBits channels, ?_⟩
  rintro rate (rfl | hrate)
  · exact CompoundChannel.informationCapacityBits_nonnegative channels
  · exact achievableRate_le_informationCapacityBits channels hrate

/-- The converse for the operational supremum, including its explicit zero rate. -/
theorem operationalCapacityBits_le_informationCapacityBits [Nonempty S] [Nonempty X]
    (channels : S → FiniteChannel X Y) :
    CompoundChannel.operationalCapacityBits channels ≤
      CompoundChannel.informationCapacityBits channels := by
  apply csSup_le
  · exact ⟨0, Or.inl rfl⟩
  · rintro rate (rfl | hrate)
    · exact CompoundChannel.informationCapacityBits_nonnegative channels
    · exact achievableRate_le_informationCapacityBits channels hrate

end CapacityAtlasCompound

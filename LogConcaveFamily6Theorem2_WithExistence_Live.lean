import Mathlib
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.NhdsWithin
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Push
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Order.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Bound
import Mathlib.Order.Filter.AtTopBot.Field

set_option linter.all false

noncomputable section

/-!
# The family-(6) extremum: standalone Live Lean source

This file has no project-local imports.  It includes the explicit
compact normalized-profile construction, the genuine global-
maximizer lemma, Claims (i)--(iii), and the sharp endpoint
witnesses.
-/

/-!
Flattened source section: ClaimsI_II_Clean.lean
-/

section FlattenedExistenceSection1

/-!
This file is mechanically flattened from the dependency closures of
`lean_i.ClaimIComplete`, `lean_ii.ClaimIILocalMax`, and
`lean_ii.ClaimIIFullFamilyBridge`. It has no project-local imports and can
be pasted into Live Lean as one file.
-/

/-! ## Flattened source: `lean_i/MomentZeros.lean` -/



open Real Set MeasureTheory intervalIntegral

namespace LogConcaveClaimI

private lemma nonneg_on_Icc_of_pos_at_of_no_zero
    {a b p : ℝ} {r : ℝ → ℝ} (hr : ContinuousOn r (Icc a b))
    (hp : p ∈ Ioo a b) (hrp : 0 < r p)
    (hzero : ∀ z ∈ Ioo a b, r z = 0 → False) :
    ∀ x ∈ Icc a b, 0 ≤ r x := by
  intro x hx
  by_contra hnonneg
  have hrx : r x < 0 := lt_of_not_ge hnonneg
  have hxpval : r x ≤ r p := (hrx.trans hrp).le
  have hsub : uIcc x p ⊆ Icc a b := uIcc_subset_Icc hx ⟨hp.1.le, hp.2.le⟩
  have hzmem : 0 ∈ r '' uIcc x p := by
    apply intermediate_value_uIcc (hr.mono hsub)
    rw [uIcc_of_le hxpval]
    exact ⟨hrx.le, hrp.le⟩
  obtain ⟨z, hz, hrz⟩ := hzmem
  have hzx : z ≠ x := by
    intro h
    subst z
    linarith
  have hzp : z ≠ p := by
    intro h
    subst z
    linarith
  have hzint : z ∈ Ioo a b := by
    by_cases hxp : x ≤ p
    · rw [uIcc_of_le hxp] at hz
      exact ⟨hx.1.trans_lt (lt_of_le_of_ne hz.1 (Ne.symm hzx)), hz.2.trans_lt hp.2⟩
    · have hpx : p ≤ x := le_of_lt (lt_of_not_ge hxp)
      rw [uIcc_of_ge hpx] at hz
      exact ⟨hp.1.trans_le hz.1, (lt_of_le_of_ne hz.2 hzx).trans_le hx.2⟩
  exact hzero z hzint hrz

private lemma nonpos_on_Icc_of_neg_at_of_no_zero
    {a b p : ℝ} {r : ℝ → ℝ} (hr : ContinuousOn r (Icc a b))
    (hp : p ∈ Ioo a b) (hrp : r p < 0)
    (hzero : ∀ z ∈ Ioo a b, r z = 0 → False) :
    ∀ x ∈ Icc a b, r x ≤ 0 := by
  have h := nonneg_on_Icc_of_pos_at_of_no_zero
    (r := fun x ↦ -r x) hr.neg hp (neg_pos.mpr hrp) (by
      intro z hz hzr
      apply hzero z hz
      linarith)
  intro x hx
  have := h x hx
  linarith

private lemma integral_mul_pos_of_weak_sign
    {a b p : ℝ} {r w : ℝ → ℝ} (hab : a < b)
    (hr : ContinuousOn r (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hp : p ∈ Ioo a b) (hrp : 0 < r p)
    (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    (hrnonneg : ∀ x ∈ Icc a b, 0 ≤ r x) :
    0 < ∫ x in a..b, r x * w x := by
  apply intervalIntegral.integral_pos hab (hr.mul hw)
  · intro x hx
    exact mul_nonneg (hrnonneg x (Ioc_subset_Icc_self hx))
      (hwpos x (Ioc_subset_Icc_self hx)).le
  · exact ⟨p, ⟨hp.1.le, hp.2.le⟩, mul_pos hrp (hwpos p ⟨hp.1.le, hp.2.le⟩)⟩

private lemma integral_mul_neg_of_weak_sign
    {a b p : ℝ} {r w : ℝ → ℝ} (hab : a < b)
    (hr : ContinuousOn r (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hp : p ∈ Ioo a b) (hrp : r p < 0)
    (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    (hrnonpos : ∀ x ∈ Icc a b, r x ≤ 0) :
    ∫ x in a..b, r x * w x < 0 := by
  have hpos : 0 < ∫ x in a..b, (-r x) * w x :=
    integral_mul_pos_of_weak_sign hab hr.neg hw hp (neg_pos.mpr hrp) hwpos
      (fun x hx ↦ neg_nonneg.mpr (hrnonpos x hx))
  have heq : (∫ x in a..b, (-r x) * w x) = -(∫ x in a..b, r x * w x) := by
    rw [← intervalIntegral.integral_neg]
    congr 1
    funext x
    ring
  linarith

private lemma exists_interior_zero_of_integral_zero
    {a b : ℝ} {r w : ℝ → ℝ} (hab : a < b)
    (hr : ContinuousOn r (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    (hzero : (∫ x in a..b, r x * w x) = 0) :
    ∃ c ∈ Ioo a b, r c = 0 := by
  let p := (a + b) / 2
  have hp : p ∈ Ioo a b := by
    dsimp [p]
    constructor <;> linarith
  by_cases hrp : r p = 0
  · exact ⟨p, hp, hrp⟩
  by_contra hnone
  push Not at hnone
  rcases lt_or_gt_of_ne hrp with hrpneg | hrppos
  · have hnonpos := nonpos_on_Icc_of_neg_at_of_no_zero hr hp hrpneg hnone
    have := integral_mul_neg_of_weak_sign hab hr hw hp hrpneg hwpos hnonpos
    linarith
  · have hnonneg := nonneg_on_Icc_of_pos_at_of_no_zero hr hp hrppos hnone
    have := integral_mul_pos_of_weak_sign hab hr hw hp hrppos hwpos hnonneg
    linarith

private lemma combined_moment_zero
    {a b c : ℝ} {r w : ℝ → ℝ}
    (hab : a ≤ b)
    (hr : ContinuousOn r (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (h₀ : (∫ x in a..b, r x * w x) = 0)
    (h₁ : (∫ x in a..b, x * r x * w x) = 0) :
    (∫ x in a..b, (x - c) * r x * w x) = 0 := by
  have hi₀ : IntervalIntegrable (fun x ↦ r x * w x) volume a b :=
    ((hr.mul hw).mono (by simpa [uIcc_of_le hab])).intervalIntegrable
  have hi₁ : IntervalIntegrable (fun x ↦ x * r x * w x) volume a b :=
    (((continuousOn_id.mul hr).mul hw).mono (by simpa [uIcc_of_le hab])).intervalIntegrable
  calc
    (∫ x in a..b, (x - c) * r x * w x) =
        (∫ x in a..b, (x * r x * w x) - c * (r x * w x)) := by
          congr 1
          funext x
          ring
    _ = (∫ x in a..b, x * r x * w x) -
        (∫ x in a..b, c * (r x * w x)) :=
          intervalIntegral.integral_sub hi₁ (hi₀.const_mul c)
    _ = 0 := by rw [intervalIntegral.integral_const_mul, h₀, h₁]; ring

/-! Two vanishing consecutive moments force two distinct interior zeros.  This is a
weighted, one-dimensional form of the Karlin--Novikoff sign-change lemma. -/
theorem two_interior_zeros_of_zero_moments
    {a b : ℝ} {r w : ℝ → ℝ} (hab : a < b)
    (hr : ContinuousOn r (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hwpos : ∀ x ∈ Icc a b, 0 < w x)
    (h₀ : (∫ x in a..b, r x * w x) = 0)
    (h₁ : (∫ x in a..b, x * r x * w x) = 0) :
    ∃ x₁ x₂, a < x₁ ∧ x₁ < x₂ ∧ x₂ < b ∧ r x₁ = 0 ∧ r x₂ = 0 := by
  obtain ⟨c, hc, hrc⟩ := exists_interior_zero_of_integral_zero hab hr hw hwpos h₀
  by_contra hnot
  have huniq : ∀ z ∈ Ioo a b, r z = 0 → z = c := by
    intro z hz hrz
    by_contra hzc
    rcases lt_or_gt_of_ne hzc with hzc | hzc
    · apply hnot
      exact ⟨z, c, hz.1, hzc, hc.2, hrz, hrc⟩
    · apply hnot
      exact ⟨c, z, hc.1, hzc, hz.2, hrc, hrz⟩
  let p := (a + c) / 2
  let q := (c + b) / 2
  have hp : p ∈ Ioo a c := by dsimp [p]; constructor <;> linarith [hc.1]
  have hq : q ∈ Ioo c b := by dsimp [q]; constructor <;> linarith [hc.2]
  have hpab : p ∈ Ioo a b := ⟨hp.1, hp.2.trans hc.2⟩
  have hqab : q ∈ Ioo a b := ⟨hc.1.trans hq.1, hq.2⟩
  have hrp : r p ≠ 0 := fun h ↦ hp.2.ne (huniq p hpab h)
  have hrq : r q ≠ 0 := fun h ↦ hq.1.ne' (huniq q hqab h)
  have hzeroL : ∀ z ∈ Ioo a c, r z = 0 → False := by
    intro z hz hrz
    exact hz.2.ne (huniq z ⟨hz.1, hz.2.trans hc.2⟩ hrz)
  have hzeroR : ∀ z ∈ Ioo c b, r z = 0 → False := by
    intro z hz hrz
    exact hz.1.ne' (huniq z ⟨hc.1.trans hz.1, hz.2⟩ hrz)
  have hrL := hr.mono (Icc_subset_Icc_right hc.2.le)
  have hrR := hr.mono (Icc_subset_Icc_left hc.1.le)
  rcases lt_or_gt_of_ne hrp with hrpneg | hrppos <;>
    rcases lt_or_gt_of_ne hrq with hrqneg | hrqpos
  · -- negative on both sides: the zeroth moment is strictly negative
    have hL := nonpos_on_Icc_of_neg_at_of_no_zero hrL hp hrpneg hzeroL
    have hR := nonpos_on_Icc_of_neg_at_of_no_zero hrR hq hrqneg hzeroR
    have hall : ∀ x ∈ Icc a b, r x ≤ 0 := by
      intro x hx
      by_cases hxc : x ≤ c
      · exact hL x ⟨hx.1, hxc⟩
      · exact hR x ⟨le_of_lt (lt_of_not_ge hxc), hx.2⟩
    have := integral_mul_neg_of_weak_sign hab hr hw hpab hrpneg hwpos hall
    linarith
  · -- negative on the left, positive on the right: `(x-c)r(x)` is nonnegative
    have hL := nonpos_on_Icc_of_neg_at_of_no_zero hrL hp hrpneg hzeroL
    have hR := nonneg_on_Icc_of_pos_at_of_no_zero hrR hq hrqpos hzeroR
    let s := fun x ↦ (x - c) * r x
    have hscont : ContinuousOn s (Icc a b) := (continuousOn_id.sub continuousOn_const).mul hr
    have hsnonneg : ∀ x ∈ Icc a b, 0 ≤ s x := by
      intro x hx
      by_cases hxc : x ≤ c
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxc) (hL x ⟨hx.1, hxc⟩)
      · exact mul_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hxc)))
          (hR x ⟨le_of_lt (lt_of_not_ge hxc), hx.2⟩)
    have hsp : 0 < s p := mul_pos_of_neg_of_neg (sub_neg.mpr hp.2) hrpneg
    have hpos := integral_mul_pos_of_weak_sign hab hscont hw hpab hsp hwpos hsnonneg
    have hz := combined_moment_zero hab.le hr hw h₀ h₁ (c := c)
    exact (ne_of_gt hpos) (by simpa [s, mul_assoc] using hz)
  · -- positive on the left, negative on the right: `(x-c)r(x)` is nonpositive
    have hL := nonneg_on_Icc_of_pos_at_of_no_zero hrL hp hrppos hzeroL
    have hR := nonpos_on_Icc_of_neg_at_of_no_zero hrR hq hrqneg hzeroR
    let s := fun x ↦ (x - c) * r x
    have hscont : ContinuousOn s (Icc a b) := (continuousOn_id.sub continuousOn_const).mul hr
    have hsnonpos : ∀ x ∈ Icc a b, s x ≤ 0 := by
      intro x hx
      by_cases hxc : x ≤ c
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxc) (hL x ⟨hx.1, hxc⟩)
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hxc)))
          (hR x ⟨le_of_lt (lt_of_not_ge hxc), hx.2⟩)
    have hsp : s p < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hp.2) hrppos
    have hneg := integral_mul_neg_of_weak_sign hab hscont hw hpab hsp hwpos hsnonpos
    have hz := combined_moment_zero hab.le hr hw h₀ h₁ (c := c)
    exact (ne_of_lt hneg) (by simpa [s, mul_assoc] using hz)
  · -- positive on both sides: the zeroth moment is strictly positive
    have hL := nonneg_on_Icc_of_pos_at_of_no_zero hrL hp hrppos hzeroL
    have hR := nonneg_on_Icc_of_pos_at_of_no_zero hrR hq hrqpos hzeroR
    have hall : ∀ x ∈ Icc a b, 0 ≤ r x := by
      intro x hx
      by_cases hxc : x ≤ c
      · exact hL x ⟨hx.1, hxc⟩
      · exact hR x ⟨le_of_lt (lt_of_not_ge hxc), hx.2⟩
    have := integral_mul_pos_of_weak_sign hab hr hw hpab hrppos hwpos hall
    linarith

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/ResidualProfile.lean` -/



open Real Set

namespace LogConcaveClaimI

/-! The one-variable profile controlling the derivative of the Lagrange residual. -/

def bracket (alpha A B t : ℝ) : ℝ := A * exp (-alpha * t) + B

def profile (alpha A B t : ℝ) : ℝ := t * bracket alpha A B t

def turningProfile (alpha A t : ℝ) : ℝ :=
  A * exp (-alpha * t) * (alpha * t - 1)

lemma hasDerivAt_bracket (alpha A B t : ℝ) :
    HasDerivAt (bracket alpha A B) (-A * alpha * exp (-alpha * t)) t := by
  have hinner : HasDerivAt (fun x : ℝ ↦ -alpha * x) (-alpha) t :=
    by simpa only [mul_one] using (hasDerivAt_id' t).const_mul (-alpha)
  have hexp : HasDerivAt (fun x : ℝ ↦ exp (-alpha * x))
      (-alpha * exp (-alpha * t)) t := by
    simpa only [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (-alpha * t)).comp t hinner
  have h := (hexp.const_mul A).add (hasDerivAt_const t B)
  have hfun : bracket alpha A B =
      (fun x : ℝ ↦ A * exp (-alpha * x)) + fun _ ↦ B := by
    funext x
    rfl
  rw [hfun]
  apply h.congr_deriv
  ring

lemma hasDerivAt_profile (alpha A B t : ℝ) :
    HasDerivAt (profile alpha A B)
      (B - turningProfile alpha A t) t := by
  have h := (hasDerivAt_id' t).mul (hasDerivAt_bracket alpha A B t)
  have heq : bracket alpha A B t + t * (-A * alpha * exp (-alpha * t)) =
      B - turningProfile alpha A t := by
    simp only [bracket, turningProfile]
    ring
  have hfun : profile alpha A B = (fun x : ℝ ↦ x) * bracket alpha A B := by
    funext x
    rfl
  rw [hfun]
  apply h.congr_deriv
  simpa only [one_mul] using heq

lemma hasDerivAt_turningProfile (alpha A t : ℝ) :
    HasDerivAt (turningProfile alpha A)
      (A * alpha * exp (-alpha * t) * (2 - alpha * t)) t := by
  have he : HasDerivAt (fun x : ℝ ↦ exp (-alpha * x))
      (-alpha * exp (-alpha * t)) t := by
    have hinner : HasDerivAt (fun x : ℝ ↦ -alpha * x) (-alpha) t := by
      simpa only [mul_one] using (hasDerivAt_id' t).const_mul (-alpha)
    simpa only [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (-alpha * t)).comp t
        hinner
  have hf : HasDerivAt (fun x : ℝ ↦ A * exp (-alpha * x))
      (A * (-alpha * exp (-alpha * t))) t := he.const_mul A
  have hl : HasDerivAt (fun x : ℝ ↦ alpha * x - 1) alpha t := by
    simpa only [mul_one] using ((hasDerivAt_id' t).const_mul alpha).sub_const 1
  have h := hf.mul hl
  have heq : A * (-alpha * exp (-alpha * t)) * (alpha * t - 1) +
      (A * exp (-alpha * t)) * alpha =
      A * alpha * exp (-alpha * t) * (2 - alpha * t) := by ring
  have hfun : turningProfile alpha A =
      (fun x : ℝ ↦ A * exp (-alpha * x)) * (fun x ↦ alpha * x - 1) := by
    funext x
    rfl
  rw [hfun]
  exact h.congr_deriv heq

lemma continuous_profile (alpha A B : ℝ) : Continuous (profile alpha A B) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_profile alpha A B t).continuousAt

lemma continuous_turningProfile (alpha A : ℝ) :
    Continuous (turningProfile alpha A) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_turningProfile alpha A t).continuousAt

lemma turningProfile_strictMonoOn_left {alpha A : ℝ}
    (halpha : 0 < alpha) (hA : 0 < A) :
    StrictMonoOn (turningProfile alpha A) (Iic (2 / alpha)) := by
  apply strictMonoOn_of_deriv_pos (convex_Iic (2 / alpha))
    (continuous_turningProfile alpha A).continuousOn
  intro t ht
  rw [(hasDerivAt_turningProfile alpha A t).deriv]
  have ht' : t < 2 / alpha := by simpa using ht
  have hfactor : 0 < 2 - alpha * t := by
    have := (lt_div_iff₀ halpha).1 ht'
    nlinarith
  positivity

lemma turningProfile_strictAntiOn_right {alpha A : ℝ}
    (halpha : 0 < alpha) (hA : 0 < A) :
    StrictAntiOn (turningProfile alpha A) (Ici (2 / alpha)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (2 / alpha))
    (continuous_turningProfile alpha A).continuousOn
  intro t ht
  rw [(hasDerivAt_turningProfile alpha A t).deriv]
  have ht' : 2 / alpha < t := by simpa using ht
  have hfactor : 2 - alpha * t < 0 := by
    have := (div_lt_iff₀ halpha).1 ht'
    nlinarith
  have hpos : 0 < A * alpha * exp (-alpha * t) := by positivity
  exact mul_neg_of_pos_of_neg hpos hfactor

lemma bracket_strictAnti {alpha A B : ℝ}
    (halpha : 0 < alpha) (hA : 0 < A) :
    StrictAnti (bracket alpha A B) := by
  apply strictAnti_of_deriv_neg
  intro t
  rw [(hasDerivAt_bracket alpha A B t).deriv]
  have : 0 < A * alpha * exp (-alpha * t) := by positivity
  nlinarith

lemma exists_profile_deriv_zero {alpha A B x y : ℝ} (hxy : x < y)
    (heq : profile alpha A B x = profile alpha A B y) :
    ∃ z ∈ Ioo x y, deriv (profile alpha A B) z = 0 := by
  obtain ⟨z, hz, hder⟩ := exists_deriv_eq_slope (profile alpha A B) hxy
    (continuous_profile alpha A B).continuousOn
    (fun t _ ↦ (hasDerivAt_profile alpha A B t).differentiableAt.differentiableWithinAt)
  refine ⟨z, hz, ?_⟩
  rw [hder, heq, sub_self, zero_div]

lemma turningProfile_eq_of_profile_deriv_zero {alpha A B t : ℝ}
    (hzero : deriv (profile alpha A B) t = 0) :
    turningProfile alpha A t = B := by
  rw [(hasDerivAt_profile alpha A B t).deriv] at hzero
  linarith

/-! If `B ≥ 0`, a horizontal line meets the positive-half-line profile at most three
times.  The formulation below is exactly the ordered-root statement needed later. -/
lemma no_four_profile_roots_of_B_nonneg {alpha A B c t₁ t₂ t₃ t₄ : ℝ}
    (halpha : 0 < alpha) (hA : 0 < A) (hB : 0 ≤ B)
    (ht₁ : 0 < t₁) (h₁₂ : t₁ < t₂) (h₂₃ : t₂ < t₃) (h₃₄ : t₃ < t₄)
    (hr₁ : profile alpha A B t₁ = c) (hr₂ : profile alpha A B t₂ = c)
    (hr₃ : profile alpha A B t₃ = c) (hr₄ : profile alpha A B t₄ = c) : False := by
  obtain ⟨u, hu, hu0⟩ := exists_profile_deriv_zero h₁₂ (hr₁.trans hr₂.symm)
  obtain ⟨v, hv, hv0⟩ := exists_profile_deriv_zero h₂₃ (hr₂.trans hr₃.symm)
  obtain ⟨w, hw, hw0⟩ := exists_profile_deriv_zero h₃₄ (hr₃.trans hr₄.symm)
  have huv : u < v := hu.2.trans hv.1
  have hvw : v < w := hv.2.trans hw.1
  have huB := turningProfile_eq_of_profile_deriv_zero hu0
  have hvB := turningProfile_eq_of_profile_deriv_zero hv0
  have hwB := turningProfile_eq_of_profile_deriv_zero hw0
  by_cases hvp : v ≤ 2 / alpha
  · have hlt := turningProfile_strictMonoOn_left halpha hA (le_trans huv.le hvp) hvp huv
    exact (ne_of_lt hlt) (huB.trans hvB.symm)
  · have hpv : 2 / alpha ≤ v := le_of_lt (lt_of_not_ge hvp)
    have hlt := turningProfile_strictAntiOn_right halpha hA hpv
      (le_trans hpv hvw.le) hvw
    exact (ne_of_gt hlt) (hvB.trans hwB.symm)

/-! If `B < 0`, a positive horizontal line meets the profile at most twice. -/
lemma no_three_profile_roots_of_B_neg_of_level_pos
    {alpha A B c t₁ t₂ t₃ : ℝ}
    (halpha : 0 < alpha) (hA : 0 < A) (hB : B < 0) (hc : 0 < c)
    (ht₁ : 0 < t₁) (h₁₂ : t₁ < t₂) (h₂₃ : t₂ < t₃)
    (hr₁ : profile alpha A B t₁ = c) (hr₂ : profile alpha A B t₂ = c)
    (hr₃ : profile alpha A B t₃ = c) : False := by
  obtain ⟨u, hu, hu0⟩ := exists_profile_deriv_zero h₁₂ (hr₁.trans hr₂.symm)
  obtain ⟨v, hv, hv0⟩ := exists_profile_deriv_zero h₂₃ (hr₂.trans hr₃.symm)
  have huv : u < v := hu.2.trans hv.1
  have huB := turningProfile_eq_of_profile_deriv_zero hu0
  have hvB := turningProfile_eq_of_profile_deriv_zero hv0
  have hu_one : u < 1 / alpha := by
    by_contra h
    have hfac : 0 ≤ alpha * u - 1 := by
      rw [sub_nonneg]
      have hu_ge : 1 / alpha ≤ u := le_of_not_gt h
      simpa [mul_comm] using (div_le_iff₀ halpha).1 hu_ge
    have : 0 ≤ turningProfile alpha A u := by
      simp only [turningProfile]
      positivity
    linarith
  have hv_one : v < 1 / alpha := by
    by_contra h
    have hfac : 0 ≤ alpha * v - 1 := by
      rw [sub_nonneg]
      have hv_ge : 1 / alpha ≤ v := le_of_not_gt h
      simpa [mul_comm] using (div_le_iff₀ halpha).1 hv_ge
    have : 0 ≤ turningProfile alpha A v := by
      simp only [turningProfile]
      positivity
    linarith
  have hone_two : 1 / alpha ≤ 2 / alpha := by
    exact (div_le_div_iff_of_pos_right halpha).2 one_le_two
  have hlt := turningProfile_strictMonoOn_left halpha hA
    (le_trans hu_one.le hone_two) (le_trans hv_one.le hone_two) huv
  exact (ne_of_lt hlt) (huB.trans hvB.symm)

lemma bracket_eq_div_of_profile_eq {alpha A B c t : ℝ} (ht : 0 < t)
    (h : profile alpha A B t = c) : bracket alpha A B t = c / t := by
  apply (eq_div_iff ht.ne').2
  simpa [profile, mul_comm] using h

/-! If `B < 0`, a nonpositive horizontal line meets the positive-half-line profile at
most once (apart from the origin, which is excluded by `0 < t₁`). -/
lemma no_two_profile_roots_of_B_neg_of_level_nonpos
    {alpha A B c t₁ t₂ : ℝ}
    (halpha : 0 < alpha) (hA : 0 < A) (hB : B < 0) (hc : c ≤ 0)
    (ht₁ : 0 < t₁) (h₁₂ : t₁ < t₂)
    (hr₁ : profile alpha A B t₁ = c) (hr₂ : profile alpha A B t₂ = c) : False := by
  have hbr : bracket alpha A B t₂ < bracket alpha A B t₁ :=
    bracket_strictAnti halpha hA h₁₂
  by_cases hc0 : c = 0
  · have hb₁ : bracket alpha A B t₁ = 0 := by
      rw [bracket_eq_div_of_profile_eq ht₁ hr₁, hc0, zero_div]
    have hb₂ : bracket alpha A B t₂ = 0 := by
      rw [bracket_eq_div_of_profile_eq (ht₁.trans h₁₂) hr₂, hc0, zero_div]
    linarith
  · have hcneg : c < 0 := lt_of_le_of_ne hc hc0
    have hi : t₂⁻¹ < t₁⁻¹ := (inv_lt_inv₀ (ht₁.trans h₁₂) ht₁).2 h₁₂
    have hdiv : c / t₁ < c / t₂ := by
      simpa [div_eq_mul_inv] using mul_lt_mul_of_neg_left hi hcneg
    rw [bracket_eq_div_of_profile_eq ht₁ hr₁,
      bracket_eq_div_of_profile_eq (ht₁.trans h₁₂) hr₂] at hbr
    linarith

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/ResidualSlope.lean` -/



open Real Set

namespace LogConcaveClaimI

/-! The odd part of the derivative of the Lagrange residual. -/

def oddSlope (alpha A B x : ℝ) : ℝ :=
  -x * bracket alpha A B |x|

lemma oddSlope_of_neg {alpha A B x : ℝ} (hx : x < 0) :
    oddSlope alpha A B x = profile alpha A B (-x) := by
  simp [oddSlope, profile, abs_of_neg hx, neg_mul]

lemma oddSlope_of_pos {alpha A B x : ℝ} (hx : 0 < x) :
    oddSlope alpha A B x = -profile alpha A B x := by
  simp [oddSlope, profile, abs_of_pos hx]

lemma bracket_pos_of_B_nonneg {alpha A B t : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) : 0 < bracket alpha A B t := by
  simp only [bracket]
  have : 0 < A * exp (-alpha * t) := by positivity
  linarith

lemma oddSlope_pos_of_neg_of_B_nonneg {alpha A B x : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hx : x < 0) :
    0 < oddSlope alpha A B x := by
  rw [oddSlope]
  exact mul_pos (neg_pos.mpr hx) (bracket_pos_of_B_nonneg hA hB)

lemma oddSlope_neg_of_pos_of_B_nonneg {alpha A B x : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hx : 0 < x) :
    oddSlope alpha A B x < 0 := by
  rw [oddSlope]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hx) (bracket_pos_of_B_nonneg hA hB)

private lemma root_neg_of_B_nonneg_of_level_pos {alpha A B c x : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hc : 0 < c)
    (hx : oddSlope alpha A B x = c) : x < 0 := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · exact hneg
  · subst x
    simp [oddSlope] at hx
    linarith
  · have := oddSlope_neg_of_pos_of_B_nonneg (alpha := alpha) hA hB hpos
    linarith

private lemma root_pos_of_B_nonneg_of_level_neg {alpha A B c x : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hc : c < 0)
    (hx : oddSlope alpha A B x = c) : 0 < x := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have := oddSlope_pos_of_neg_of_B_nonneg (alpha := alpha) hA hB hneg
    linarith
  · subst x
    simp [oddSlope] at hx
    linarith
  · exact hpos

/-! Every horizontal line meets `oddSlope` in at most three points.  This is the exact
ordered-root form that combines smoothly with four applications of Rolle's theorem. -/
theorem no_four_oddSlope_roots {alpha A B c x₁ x₂ x₃ x₄ : ℝ}
    (halpha : 0 < alpha) (hA : 0 < A)
    (h₁₂ : x₁ < x₂) (h₂₃ : x₂ < x₃) (h₃₄ : x₃ < x₄)
    (hr₁ : oddSlope alpha A B x₁ = c)
    (hr₂ : oddSlope alpha A B x₂ = c)
    (hr₃ : oddSlope alpha A B x₃ = c)
    (hr₄ : oddSlope alpha A B x₄ = c) : False := by
  by_cases hB : 0 ≤ B
  · rcases lt_trichotomy c 0 with hc | hc | hc
    · have hx₁ := root_pos_of_B_nonneg_of_level_neg hA hB hc hr₁
      have hx₂ := root_pos_of_B_nonneg_of_level_neg hA hB hc hr₂
      have hx₃ := root_pos_of_B_nonneg_of_level_neg hA hB hc hr₃
      have hx₄ := root_pos_of_B_nonneg_of_level_neg hA hB hc hr₄
      apply no_four_profile_roots_of_B_nonneg halpha hA hB hx₁ h₁₂ h₂₃ h₃₄
        (c := -c)
      · simpa [oddSlope_of_pos hx₁] using congrArg Neg.neg hr₁
      · simpa [oddSlope_of_pos hx₂] using congrArg Neg.neg hr₂
      · simpa [oddSlope_of_pos hx₃] using congrArg Neg.neg hr₃
      · simpa [oddSlope_of_pos hx₄] using congrArg Neg.neg hr₄
    · have hr₁0 : oddSlope alpha A B x₁ = 0 := hr₁.trans hc
      have hr₂0 : oddSlope alpha A B x₂ = 0 := hr₂.trans hc
      have hx₁ : x₁ = 0 := by
        rcases lt_trichotomy x₁ 0 with hn | hz | hp
        · have := oddSlope_pos_of_neg_of_B_nonneg (alpha := alpha) hA hB hn
          linarith
        · exact hz
        · have := oddSlope_neg_of_pos_of_B_nonneg (alpha := alpha) hA hB hp
          linarith
      have hx₂ : x₂ = 0 := by
        rcases lt_trichotomy x₂ 0 with hn | hz | hp
        · have := oddSlope_pos_of_neg_of_B_nonneg (alpha := alpha) hA hB hn
          linarith
        · exact hz
        · have := oddSlope_neg_of_pos_of_B_nonneg (alpha := alpha) hA hB hp
          linarith
      linarith
    · have hx₁ := root_neg_of_B_nonneg_of_level_pos hA hB hc hr₁
      have hx₂ := root_neg_of_B_nonneg_of_level_pos hA hB hc hr₂
      have hx₃ := root_neg_of_B_nonneg_of_level_pos hA hB hc hr₃
      have hx₄ := root_neg_of_B_nonneg_of_level_pos hA hB hc hr₄
      apply no_four_profile_roots_of_B_nonneg halpha hA hB (neg_pos.mpr hx₄)
        (neg_lt_neg h₃₄) (neg_lt_neg h₂₃) (neg_lt_neg h₁₂) (c := c)
      · simpa [oddSlope_of_neg hx₄] using hr₄
      · simpa [oddSlope_of_neg hx₃] using hr₃
      · simpa [oddSlope_of_neg hx₂] using hr₂
      · simpa [oddSlope_of_neg hx₁] using hr₁
  · have hBneg : B < 0 := lt_of_not_ge hB
    rcases lt_trichotomy c 0 with hc | hc | hc
    · by_cases hx₂ : 0 < x₂
      · have hx₃ : 0 < x₃ := hx₂.trans h₂₃
        have hx₄ : 0 < x₄ := hx₃.trans h₃₄
        apply no_three_profile_roots_of_B_neg_of_level_pos halpha hA hBneg
          (neg_pos.mpr hc) hx₂ h₂₃ h₃₄ (c := -c)
        · simpa [oddSlope_of_pos hx₂] using congrArg Neg.neg hr₂
        · simpa [oddSlope_of_pos hx₃] using congrArg Neg.neg hr₃
        · simpa [oddSlope_of_pos hx₄] using congrArg Neg.neg hr₄
      · have hx₂' : x₂ < 0 := by
          rcases lt_or_eq_of_le (le_of_not_gt hx₂) with hn | hz
          · exact hn
          · subst x₂
            simp [oddSlope] at hr₂
            linarith
        have hx₁ : x₁ < 0 := h₁₂.trans hx₂'
        apply no_two_profile_roots_of_B_neg_of_level_nonpos halpha hA hBneg (le_of_lt hc)
          (neg_pos.mpr hx₂') (neg_lt_neg h₁₂) (c := c)
        · simpa [oddSlope_of_neg hx₂'] using hr₂
        · simpa [oddSlope_of_neg hx₁] using hr₁
    · have hr₁0 : oddSlope alpha A B x₁ = 0 := hr₁.trans hc
      have hr₂0 : oddSlope alpha A B x₂ = 0 := hr₂.trans hc
      have hr₃0 : oddSlope alpha A B x₃ = 0 := hr₃.trans hc
      have hr₄0 : oddSlope alpha A B x₄ = 0 := hr₄.trans hc
      rcases lt_trichotomy x₂ 0 with hx₂ | hx₂ | hx₂
      · have hx₁ : x₁ < 0 := h₁₂.trans hx₂
        apply no_two_profile_roots_of_B_neg_of_level_nonpos halpha hA hBneg le_rfl
          (neg_pos.mpr hx₂) (neg_lt_neg h₁₂) (c := 0)
        · simpa [oddSlope_of_neg hx₂] using hr₂0
        · simpa [oddSlope_of_neg hx₁] using hr₁0
      · subst x₂
        have hx₃ : 0 < x₃ := h₂₃
        have hx₄ : 0 < x₄ := hx₃.trans h₃₄
        apply no_two_profile_roots_of_B_neg_of_level_nonpos halpha hA hBneg le_rfl
          hx₃ h₃₄ (c := 0)
        · simpa [oddSlope_of_pos hx₃] using congrArg Neg.neg hr₃0
        · simpa [oddSlope_of_pos hx₄] using congrArg Neg.neg hr₄0
      · have hx₃ : 0 < x₃ := hx₂.trans h₂₃
        apply no_two_profile_roots_of_B_neg_of_level_nonpos halpha hA hBneg le_rfl
          hx₂ h₂₃ (c := 0)
        · simpa [oddSlope_of_pos hx₂] using congrArg Neg.neg hr₂0
        · simpa [oddSlope_of_pos hx₃] using congrArg Neg.neg hr₃0
    · by_cases hx₃ : x₃ < 0
      · have hx₂ : x₂ < 0 := h₂₃.trans hx₃
        have hx₁ : x₁ < 0 := h₁₂.trans hx₂
        apply no_three_profile_roots_of_B_neg_of_level_pos halpha hA hBneg hc
          (neg_pos.mpr hx₃) (neg_lt_neg h₂₃) (neg_lt_neg h₁₂) (c := c)
        · simpa [oddSlope_of_neg hx₃] using hr₃
        · simpa [oddSlope_of_neg hx₂] using hr₂
        · simpa [oddSlope_of_neg hx₁] using hr₁
      · have hx₃' : 0 < x₃ := by
          rcases lt_or_eq_of_le (le_of_not_gt hx₃) with hp | hz
          · exact hp
          · subst x₃
            simp [oddSlope] at hr₃
            linarith
        have hx₄ : 0 < x₄ := hx₃'.trans h₃₄
        apply no_two_profile_roots_of_B_neg_of_level_nonpos halpha hA hBneg
          (le_of_lt (neg_neg_of_pos hc)) hx₃' h₃₄ (c := -c)
        · simpa [oddSlope_of_pos hx₃'] using congrArg Neg.neg hr₃
        · simpa [oddSlope_of_pos hx₄] using congrArg Neg.neg hr₄

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/ResidualRolle.lean` -/



open Real Set

namespace LogConcaveClaimI

def gAlpha (alpha x : ℝ) : ℝ :=
  (1 + alpha * |x|) * exp (-alpha * |x|)

def gAlphaDeriv (alpha x : ℝ) : ℝ :=
  -(alpha ^ 2) * x * exp (-alpha * |x|)

lemma continuous_gAlpha (alpha : ℝ) : Continuous (gAlpha alpha) := by
  change Continuous (fun x : ℝ ↦ (1 + alpha * |x|) * exp (-alpha * |x|))
  fun_prop

lemma continuous_gAlphaDeriv (alpha : ℝ) : Continuous (gAlphaDeriv alpha) := by
  change Continuous (fun x : ℝ ↦ -(alpha ^ 2) * x * exp (-alpha * |x|))
  fun_prop

private lemma hasDerivAt_gAlpha_of_ne (alpha : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (gAlpha alpha) (gAlphaDeriv alpha x) x := by
  rcases hx.lt_or_gt with hxneg | hxpos
  · have hfac : HasDerivAt (fun y : ℝ ↦ 1 + (-alpha) * y) (-alpha) x :=
      (hasDerivAt_const_mul (-alpha)).const_add 1
    have he : HasDerivAt (fun y : ℝ ↦ exp (alpha * y))
        (exp (alpha * x) * alpha) x :=
      (hasDerivAt_const_mul alpha).exp
    have hf := hfac.mul he
    have hf' : HasDerivAt
        (fun y : ℝ ↦ (1 + (-alpha) * y) * exp (alpha * y))
        (gAlphaDeriv alpha x) x := hf.congr_deriv (by
          simp only [gAlphaDeriv, abs_of_neg hxneg]
          ring_nf)
    apply hf'.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxneg] with y hy
    have hy' : y < 0 := hy
    rw [gAlpha, abs_of_neg hy']
    ring_nf
  · have hfac : HasDerivAt (fun y : ℝ ↦ 1 + alpha * y) alpha x :=
      (hasDerivAt_const_mul alpha).const_add 1
    have he : HasDerivAt (fun y : ℝ ↦ exp ((-alpha) * y))
        (exp ((-alpha) * x) * (-alpha)) x :=
      (hasDerivAt_const_mul (-alpha)).exp
    have hf := hfac.mul he
    have hf' : HasDerivAt
        (fun y : ℝ ↦ (1 + alpha * y) * exp ((-alpha) * y))
        (gAlphaDeriv alpha x) x := hf.congr_deriv (by
          simp only [gAlphaDeriv, abs_of_pos hxpos]
          ring)
    apply hf'.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hxpos] with y hy
    have hy' : 0 < y := hy
    rw [gAlpha, abs_of_pos hy']

lemma hasDerivAt_gAlpha (alpha x : ℝ) :
    HasDerivAt (gAlpha alpha) (gAlphaDeriv alpha x) x := by
  apply hasDerivAt_of_hasDerivAt_of_ne' (x := 0)
    (fun y hy ↦ hasDerivAt_gAlpha_of_ne alpha hy)
    (continuous_gAlpha alpha).continuousAt
    (continuous_gAlphaDeriv alpha).continuousAt

def residual (alpha lambda₀ lambda₁ lambda₂ x : ℝ) : ℝ :=
  gAlpha alpha x - lambda₀ - lambda₁ * x - lambda₂ * x ^ 2

lemma continuous_residual (alpha lambda₀ lambda₁ lambda₂ : ℝ) :
    Continuous (residual alpha lambda₀ lambda₁ lambda₂) := by
  exact ((((continuous_gAlpha alpha).sub continuous_const).sub
    (continuous_const.mul continuous_id)).sub
      (continuous_const.mul (continuous_id.pow 2)))

lemma hasDerivAt_residual (alpha lambda₀ lambda₁ lambda₂ x : ℝ) :
    HasDerivAt (residual alpha lambda₀ lambda₁ lambda₂)
      (-lambda₁ + oddSlope alpha (alpha ^ 2) (2 * lambda₂) x) x := by
  have hlin : HasDerivAt (fun y : ℝ ↦ lambda₁ * y) lambda₁ x :=
    hasDerivAt_const_mul lambda₁
  have hquad : HasDerivAt (fun y : ℝ ↦ lambda₂ * y ^ 2)
      (lambda₂ * (2 * x)) x := by
    exact ((hasDerivAt_id' x).pow 2).const_mul lambda₂ |>.congr_deriv (by ring)
  have h := (((hasDerivAt_gAlpha alpha x).sub_const lambda₀).sub hlin).sub hquad
  apply h.congr_deriv
  simp only [gAlphaDeriv, oddSlope, bracket]
  ring

private lemma exists_residual_deriv_zero
    {alpha lambda₀ lambda₁ lambda₂ x y : ℝ} (hxy : x < y)
    (heq : residual alpha lambda₀ lambda₁ lambda₂ x =
      residual alpha lambda₀ lambda₁ lambda₂ y) :
    ∃ z ∈ Ioo x y, deriv (residual alpha lambda₀ lambda₁ lambda₂) z = 0 := by
  obtain ⟨z, hz, hder⟩ := exists_deriv_eq_slope
    (residual alpha lambda₀ lambda₁ lambda₂) hxy
    (continuous_residual alpha lambda₀ lambda₁ lambda₂).continuousOn
    (fun t _ ↦ (hasDerivAt_residual alpha lambda₀ lambda₁ lambda₂ t).differentiableAt
      |>.differentiableWithinAt)
  refine ⟨z, hz, ?_⟩
  rw [hder, heq, sub_self, zero_div]

/-! The Lagrange residual cannot have five ordered zeros. -/
theorem no_five_residual_zeros
    {alpha lambda₀ lambda₁ lambda₂ x₀ x₁ x₂ x₃ x₄ : ℝ}
    (halpha : 0 < alpha)
    (h₀₁ : x₀ < x₁) (h₁₂ : x₁ < x₂) (h₂₃ : x₂ < x₃) (h₃₄ : x₃ < x₄)
    (hr₀ : residual alpha lambda₀ lambda₁ lambda₂ x₀ = 0)
    (hr₁ : residual alpha lambda₀ lambda₁ lambda₂ x₁ = 0)
    (hr₂ : residual alpha lambda₀ lambda₁ lambda₂ x₂ = 0)
    (hr₃ : residual alpha lambda₀ lambda₁ lambda₂ x₃ = 0)
    (hr₄ : residual alpha lambda₀ lambda₁ lambda₂ x₄ = 0) : False := by
  obtain ⟨y₁, hy₁, hy₁0⟩ := exists_residual_deriv_zero h₀₁ (hr₀.trans hr₁.symm)
  obtain ⟨y₂, hy₂, hy₂0⟩ := exists_residual_deriv_zero h₁₂ (hr₁.trans hr₂.symm)
  obtain ⟨y₃, hy₃, hy₃0⟩ := exists_residual_deriv_zero h₂₃ (hr₂.trans hr₃.symm)
  obtain ⟨y₄, hy₄, hy₄0⟩ := exists_residual_deriv_zero h₃₄ (hr₃.trans hr₄.symm)
  have hslope : ∀ y, deriv (residual alpha lambda₀ lambda₁ lambda₂) y = 0 →
      oddSlope alpha (alpha ^ 2) (2 * lambda₂) y = lambda₁ := by
    intro y hy
    rw [(hasDerivAt_residual alpha lambda₀ lambda₁ lambda₂ y).deriv] at hy
    linarith
  exact no_four_oddSlope_roots halpha (sq_pos_of_pos halpha)
    (hy₁.2.trans hy₂.1) (hy₂.2.trans hy₃.1) (hy₃.2.trans hy₄.1)
    (hslope y₁ hy₁0) (hslope y₂ hy₂0) (hslope y₃ hy₃0) (hslope y₄ hy₄0)

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/CompactContradiction.lean` -/



open Real Set MeasureTheory intervalIntegral

namespace LogConcaveClaimI

/-! The deterministic contradiction at the end of Claim (i), for finite endpoints.  The
weight is left abstract because only continuity and strict positivity are used. -/
theorem compact_genuine_kink_contradiction
    {alpha A m B lambda₀ lambda₁ lambda₂ : ℝ} {w : ℝ → ℝ}
    (halpha : 0 < alpha) (hAm : A < m) (hmB : m < B)
    (hw : ContinuousOn w (Icc A B))
    (hwpos : ∀ x ∈ Icc A B, 0 < w x)
    (hL₀ : (∫ x in A..m, residual alpha lambda₀ lambda₁ lambda₂ x * w x) = 0)
    (hL₁ : (∫ x in A..m, x * residual alpha lambda₀ lambda₁ lambda₂ x * w x) = 0)
    (hR₀ : (∫ x in m..B, residual alpha lambda₀ lambda₁ lambda₂ x * w x) = 0)
    (hR₁ : (∫ x in m..B, x * residual alpha lambda₀ lambda₁ lambda₂ x * w x) = 0)
    (hendpoint : residual alpha lambda₀ lambda₁ lambda₂ A = 0 ∨
      residual alpha lambda₀ lambda₁ lambda₂ B = 0) : False := by
  let r := residual alpha lambda₀ lambda₁ lambda₂
  have hr : Continuous r := continuous_residual alpha lambda₀ lambda₁ lambda₂
  obtain ⟨x₁, x₂, hAx₁, hx₁x₂, hx₂m, hrx₁, hrx₂⟩ :=
    two_interior_zeros_of_zero_moments hAm hr.continuousOn
      (hw.mono (Icc_subset_Icc_right hmB.le))
      (fun x hx ↦ hwpos x ⟨hx.1, hx.2.trans hmB.le⟩) hL₀ hL₁
  obtain ⟨y₁, y₂, hmy₁, hy₁y₂, hy₂B, hry₁, hry₂⟩ :=
    two_interior_zeros_of_zero_moments hmB hr.continuousOn
      (hw.mono (Icc_subset_Icc_left hAm.le))
      (fun x hx ↦ hwpos x ⟨hAm.le.trans hx.1, hx.2⟩) hR₀ hR₁
  rcases hendpoint with hA | hB
  · exact no_five_residual_zeros halpha hAx₁ hx₁x₂ (hx₂m.trans hmy₁) hy₁y₂
      hA hrx₁ hrx₂ hry₁ hry₂
  · exact no_five_residual_zeros halpha hx₁x₂ (hx₂m.trans hmy₁) hy₁y₂ hy₂B
      hrx₁ hrx₂ hry₁ hry₂ hB

theorem compact_genuine_kink_contradiction_two_weights
    {alpha A m B lambda₀ lambda₁ lambda₂ : ℝ} {wL wR : ℝ → ℝ}
    (halpha : 0 < alpha) (hAm : A < m) (hmB : m < B)
    (hwL : ContinuousOn wL (Icc A m)) (hwR : ContinuousOn wR (Icc m B))
    (hwposL : ∀ x ∈ Icc A m, 0 < wL x)
    (hwposR : ∀ x ∈ Icc m B, 0 < wR x)
    (hL₀ : (∫ x in A..m, residual alpha lambda₀ lambda₁ lambda₂ x * wL x) = 0)
    (hL₁ : (∫ x in A..m, x * residual alpha lambda₀ lambda₁ lambda₂ x * wL x) = 0)
    (hR₀ : (∫ x in m..B, residual alpha lambda₀ lambda₁ lambda₂ x * wR x) = 0)
    (hR₁ : (∫ x in m..B, x * residual alpha lambda₀ lambda₁ lambda₂ x * wR x) = 0)
    (hendpoint : residual alpha lambda₀ lambda₁ lambda₂ A = 0 ∨
      residual alpha lambda₀ lambda₁ lambda₂ B = 0) : False := by
  let r := residual alpha lambda₀ lambda₁ lambda₂
  have hr : Continuous r := continuous_residual alpha lambda₀ lambda₁ lambda₂
  obtain ⟨x₁, x₂, hAx₁, hx₁x₂, hx₂m, hrx₁, hrx₂⟩ :=
    two_interior_zeros_of_zero_moments hAm hr.continuousOn hwL hwposL hL₀ hL₁
  obtain ⟨y₁, y₂, hmy₁, hy₁y₂, hy₂B, hry₁, hry₂⟩ :=
    two_interior_zeros_of_zero_moments hmB hr.continuousOn hwR hwposR hR₀ hR₁
  rcases hendpoint with hA | hB
  · exact no_five_residual_zeros halpha hAx₁ hx₁x₂ (hx₂m.trans hmy₁) hy₁y₂
      hA hrx₁ hrx₂ hry₁ hry₂
  · exact no_five_residual_zeros halpha hx₁x₂ (hx₂m.trans hmy₁) hy₁y₂ hy₂B
      hrx₁ hrx₂ hry₁ hry₂ hB

end LogConcaveClaimI

/-! ## Flattened source: `lean_core/ParametricInterval.lean` -/


/-!
# Strict differentiation of compact parametric integrals

The basic differentiation-under-the-integral theorem in mathlib produces an
ordinary Fréchet derivative.  Lagrange multipliers and the implicit function
theorem use a *strict* Fréchet derivative.  On a real Banach space, a
continuously varying derivative is strict; the first theorem below packages
this standard upgrade together with dominated convergence.

Moving endpoints are handled by the affine pullback of `[A(p), B(p)]` to the
fixed interval `[0,1]`.  This is both shorter and more robust than separately
formalizing two endpoint terms in Leibniz' rule.
-/

open Filter Set MeasureTheory
open scoped Topology Interval

namespace LogConcaveExtremum.ParametricInterval

variable {H E : Type*}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure ℝ}

/-- A dominated `C¹` integral over an arbitrary measure space is strictly
Fréchet differentiable.  This is the fixed-domain version used for half-line
tails.  The derivative is first obtained from mathlib's dominated
differentiation theorem; dominated convergence makes that derivative
continuous, hence strict. -/
theorem hasStrictFDerivAt_integral_of_dominated
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {F : H → α → E} {F' : H → α → H →L[ℝ] E}
    {x₀ : H} {U : Set H} {bound : α → ℝ}
    (hUopen : IsOpen U) (hx₀ : x₀ ∈ U)
    (hFmeas : ∀ x ∈ U, AEStronglyMeasurable (F x) ν)
    (hFint : ∀ x ∈ U, Integrable (F x) ν)
    (hF'meas : ∀ x ∈ U, AEStronglyMeasurable (F' x) ν)
    (hF'bound : ∀ᵐ t ∂ν, ∀ x ∈ U, ‖F' x t‖ ≤ bound t)
    (hbound : Integrable bound ν)
    (hFdiff : ∀ᵐ t ∂ν, ∀ x ∈ U,
      HasFDerivAt (fun y ↦ F y t) (F' x t) x)
    (hF'cont : ∀ᵐ t ∂ν, ContinuousAt (fun x ↦ F' x t) x₀) :
    HasStrictFDerivAt (fun x ↦ ∫ t, F x t ∂ν) (∫ t, F' x₀ t ∂ν) x₀ := by
  refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (f' := fun x ↦ ∫ t, F' x t ∂ν) ?_ ?_
  · filter_upwards [hUopen.mem_nhds hx₀] with x hx
    apply _root_.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (hUopen.mem_nhds hx)
    · filter_upwards [hUopen.mem_nhds hx]
      exact fun y hy ↦ hFmeas y hy
    · exact hFint x hx
    · exact hF'meas x hx
    · exact hF'bound
    · exact hbound
    · exact hFdiff
  · apply tendsto_integral_filter_of_dominated_convergence bound
    · filter_upwards [hUopen.mem_nhds hx₀] with x hx
      exact hF'meas x hx
    · filter_upwards [hUopen.mem_nhds hx₀] with x hx
      exact hF'bound.mono fun t ht ↦ ht x hx
    · exact hbound
    · exact hF'cont

/-- On a compact interval, continuity of the integrand and its pointwise
parameter derivative supplies all domination hypotheses automatically.  The
`ProperSpace` assumption is used only to make a closed parameter ball
compact; it holds for the finite-dimensional real parameter spaces used in
the application. -/
theorem hasStrictFDerivAt_intervalIntegral_of_continuous
    [ProperSpace H]
    {F : H → ℝ → E} {F' : H → ℝ → H →L[ℝ] E}
    {x₀ : H} {a b : ℝ}
    (hFcont : Continuous (Function.uncurry F))
    (hF'cont : Continuous (Function.uncurry F'))
    (hFdiff : ∀ x t, HasFDerivAt (fun y ↦ F y t) (F' x t) x) :
    HasStrictFDerivAt (fun x ↦ ∫ t in a..b, F x t)
      (∫ t in a..b, F' x₀ t) x₀ := by
  refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (f' := fun x ↦ ∫ t in a..b, F' x t) ?_ ?_
  · filter_upwards [] with x
    obtain ⟨M, hM⟩ :=
      ((isCompact_closedBall x 1).prod isCompact_uIcc).exists_bound_of_continuousOn
        hF'cont.continuousOn
    apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (bound := fun _ ↦ M) (Metric.closedBall_mem_nhds x one_pos)
    · filter_upwards [] with y
      exact (hFcont.uncurry_left y).aestronglyMeasurable
    · exact (hFcont.uncurry_left x).intervalIntegrable a b
    · exact (hF'cont.uncurry_left x).aestronglyMeasurable
    · filter_upwards [] with t ht y hy
      change ‖F' y t‖ ≤ M
      exact hM (y, t) ⟨hy, uIoc_subset_uIcc ht⟩
    · exact intervalIntegrable_const
    · filter_upwards [] with t ht y hy
      exact hFdiff y t
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hF'cont a b |>.continuousAt

/-- Joint continuity in a parameter and both endpoints. -/
theorem continuous_uncurry_intervalIntegral_of_continuous
    {F : H → ℝ → E} (hF : Continuous (Function.uncurry F)) :
    Continuous (fun v : H × (ℝ × ℝ) ↦ ∫ x in v.2.1..v.2.2, F v.1 x) := by
  have hprimitive :=
    intervalIntegral.continuous_parametric_primitive_of_continuous
      (μ := MeasureTheory.volume) (a₀ := (0 : ℝ)) hF
  have hright : Continuous
      (fun v : H × (ℝ × ℝ) ↦ ∫ x in (0 : ℝ)..v.2.2, F v.1 x) := by
    have hmap : Continuous (fun v : H × (ℝ × ℝ) ↦ (v.1, v.2.2)) :=
      continuous_fst.prodMk (continuous_snd.comp continuous_snd)
    exact hprimitive.comp hmap
  have hleft : Continuous
      (fun v : H × (ℝ × ℝ) ↦ ∫ x in (0 : ℝ)..v.2.1, F v.1 x) := by
    have hmap : Continuous (fun v : H × (ℝ × ℝ) ↦ (v.1, v.2.1)) :=
      continuous_fst.prodMk (continuous_fst.comp continuous_snd)
    exact hprimitive.comp hmap
  convert hright.sub hleft using 1
  funext v
  exact (intervalIntegral.integral_interval_sub_left
    ((hF.uncurry_left v.1).intervalIntegrable 0 v.2.2)
    ((hF.uncurry_left v.1).intervalIntegrable 0 v.2.1)).symm

/-- The endpoint part of Leibniz' rule: `(da, db)` is sent to
`db • F(p,b) - da • F(p,a)`. -/
def endpointFDeriv (F : H → ℝ → E) (p : H) (a b : ℝ) :
    (ℝ × ℝ) →L[ℝ] E :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F p b) -
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (F p a)

/-- A partial-derivative form of the parameter-dependent Leibniz rule.

The parameter partial derivative is supplied by a fixed-domain dominated
differentiation theorem.  Continuity of the integrand gives the endpoint
partial derivative by the fundamental theorem of calculus.  Continuity of
the two partial derivatives upgrades the joint map to strict
differentiability.  Unlike an affine change of variables, this statement
requires no derivative of the integrand with respect to the integration
variable. -/
theorem hasStrictFDerivAt_uncurry_intervalIntegral
    {F : H → ℝ → E}
    {Fp : H → (ℝ × ℝ) → H →L[ℝ] E} {u : H × (ℝ × ℝ)}
    (hparam : ∀ᶠ v in 𝓝 u,
      HasFDerivAt (fun p ↦ ∫ x in v.2.1..v.2.2, F p x) (Fp v.1 v.2) v.1)
    (hFcont : ∀ᶠ v in 𝓝 u, Continuous (F v.1))
    (hFpcont : ContinuousAt (Function.uncurry Fp) u)
    (hendcont : ContinuousAt
      (fun v : H × (ℝ × ℝ) ↦ endpointFDeriv F v.1 v.2.1 v.2.2) u) :
    HasStrictFDerivAt
      (fun v : H × (ℝ × ℝ) ↦ ∫ x in v.2.1..v.2.2, F v.1 x)
      ((Fp u.1 u.2).coprod (endpointFDeriv F u.1 u.2.1 u.2.2)) u := by
  apply hasStrictFDerivAt_uncurry_coprod
    (f := fun p ab ↦ ∫ x in ab.1..ab.2, F p x)
    (f₁ := Fp)
    (f₂ := fun p ab ↦ endpointFDeriv F p ab.1 ab.2)
    hparam
  · filter_upwards [hFcont] with v hv
    change HasFDerivAt
      (fun ab : ℝ × ℝ ↦ ∫ x in ab.1..ab.2, F v.1 x)
      (endpointFDeriv F v.1 v.2.1 v.2.2) v.2
    simpa only [endpointFDeriv] using
      (intervalIntegral.integral_hasStrictFDerivAt
        (hv.intervalIntegrable v.2.1 v.2.2)
        (hv.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 v.2.1))
        (hv.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 v.2.2))
        hv.continuousAt hv.continuousAt).hasFDerivAt
  · exact hFpcont
  · exact hendcont

/-- Compose the joint Leibniz rule with strictly differentiable endpoints. -/
theorem HasStrictFDerivAt.movingIntervalIntegral
    {F : H → ℝ → E} {A B : H → ℝ} {p₀ : H} {A' B' : H →L[ℝ] ℝ}
    {J' : (H × (ℝ × ℝ)) →L[ℝ] E}
    (hJ : HasStrictFDerivAt
      (fun v : H × (ℝ × ℝ) ↦ ∫ x in v.2.1..v.2.2, F v.1 x)
      J' (p₀, (A p₀, B p₀)))
    (hA : HasStrictFDerivAt A A' p₀)
    (hB : HasStrictFDerivAt B B' p₀) :
    HasStrictFDerivAt (fun p ↦ ∫ x in A p..B p, F p x)
      (J' ∘L ((ContinuousLinearMap.id ℝ H).prod (A'.prod B'))) p₀ := by
  exact hJ.comp p₀
    ((hasStrictFDerivAt_id (𝕜 := ℝ) (x := p₀)).prodMk (hA.prodMk hB))

/-- A compact, moving-endpoint Leibniz rule with assumptions phrased only as
joint continuity and a pointwise parameter derivative. -/
theorem hasStrictFDerivAt_movingIntervalIntegral_of_continuous
    [ProperSpace H]
    {F : H → ℝ → E} {F' : H → ℝ → H →L[ℝ] E}
    {A B : H → ℝ} {p₀ : H} {A' B' : H →L[ℝ] ℝ}
    (hFcont : Continuous (Function.uncurry F))
    (hF'cont : Continuous (Function.uncurry F'))
    (hFdiff : ∀ p x, HasFDerivAt (fun q ↦ F q x) (F' p x) p)
    (hA : HasStrictFDerivAt A A' p₀)
    (hB : HasStrictFDerivAt B B' p₀) :
    HasStrictFDerivAt (fun p ↦ ∫ x in A p..B p, F p x)
      (((∫ x in A p₀..B p₀, F' p₀ x).coprod
          (endpointFDeriv F p₀ (A p₀) (B p₀))) ∘L
        ((ContinuousLinearMap.id ℝ H).prod (A'.prod B'))) p₀ := by
  have hjoint : HasStrictFDerivAt
      (fun v : H × (ℝ × ℝ) ↦ ∫ x in v.2.1..v.2.2, F v.1 x)
      (((∫ x in A p₀..B p₀, F' p₀ x).coprod
        (endpointFDeriv F p₀ (A p₀) (B p₀))))
      (p₀, (A p₀, B p₀)) := by
    apply hasStrictFDerivAt_uncurry_intervalIntegral
      (F := F)
      (Fp := fun p ab ↦ ∫ x in ab.1..ab.2, F' p x)
      (u := (p₀, (A p₀, B p₀)))
    · filter_upwards [] with v
      exact (hasStrictFDerivAt_intervalIntegral_of_continuous
        (x₀ := v.1) (a := v.2.1) (b := v.2.2) hFcont hF'cont hFdiff).hasFDerivAt
    · filter_upwards [] with v
      exact hFcont.uncurry_left v.1
    · exact (continuous_uncurry_intervalIntegral_of_continuous hF'cont).continuousAt
    · have hmapR : Continuous
          (fun v : H × (ℝ × ℝ) ↦ (v.1, v.2.2)) :=
        continuous_fst.prodMk (continuous_snd.comp continuous_snd)
      have hmapL : Continuous
          (fun v : H × (ℝ × ℝ) ↦ (v.1, v.2.1)) :=
        continuous_fst.prodMk (continuous_fst.comp continuous_snd)
      have hR : Continuous
          (fun v : H × (ℝ × ℝ) ↦
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F v.1 v.2.2)) := by
        rw [show (fun v : H × (ℝ × ℝ) ↦
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (F v.1 v.2.2)) =
            (fun v ↦ ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) E)
              (ContinuousLinearMap.snd ℝ ℝ ℝ)) (F v.1 v.2.2)) by
          funext v
          exact (ContinuousLinearMap.smulRightL_apply_apply ℝ (ℝ × ℝ) E
            (ContinuousLinearMap.snd ℝ ℝ ℝ) (F v.1 v.2.2)).symm]
        exact (((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) E)
          (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous.comp
            (hFcont.comp hmapR))
      have hL : Continuous
          (fun v : H × (ℝ × ℝ) ↦
            (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (F v.1 v.2.1)) := by
        rw [show (fun v : H × (ℝ × ℝ) ↦
            (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (F v.1 v.2.1)) =
            (fun v ↦ ((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) E)
              (ContinuousLinearMap.fst ℝ ℝ ℝ)) (F v.1 v.2.1)) by
          funext v
          exact (ContinuousLinearMap.smulRightL_apply_apply ℝ (ℝ × ℝ) E
            (ContinuousLinearMap.fst ℝ ℝ ℝ) (F v.1 v.2.1)).symm]
        exact (((ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) E)
          (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous.comp
            (hFcont.comp hmapL))
      exact (hR.sub hL).continuousAt
  exact HasStrictFDerivAt.movingIntervalIntegral hjoint hA hB

/-- The fixed-interval integrand obtained from the affine map
`t ↦ A(p) + (B(p)-A(p))t`. -/
def affinePullback
    (A B : H → ℝ) (F : H → ℝ → E) (p : H) (t : ℝ) : E :=
  (B p - A p) • F p (A p + (B p - A p) * t)

/-- The affine pullback does not require an orientation hypothesis on the
endpoints; interval integrals already encode the orientation. -/
theorem integral_eq_affinePullback
    (A B : H → ℝ) (F : H → ℝ → E) (p : H) :
    (∫ x in A p..B p, F p x) = ∫ t in (0 : ℝ)..1, affinePullback A B F p t := by
  have h := intervalIntegral.smul_integral_comp_add_mul
    (f := F p) (a := (0 : ℝ)) (b := 1) (B p - A p) (A p)
  simpa [affinePullback] using h.symm

/-- Strict differentiability for an integral with moving endpoints, reduced
to strict differentiability of its affine pullback on `[0,1]`. -/
theorem hasStrictFDerivAt_movingIntegral_of_affinePullback
    {A B : H → ℝ} {F : H → ℝ → E} {p₀ : H}
    {L : H →L[ℝ] E}
    (h : HasStrictFDerivAt
      (fun p ↦ ∫ t in (0 : ℝ)..1, affinePullback A B F p t) L p₀) :
    HasStrictFDerivAt (fun p ↦ ∫ x in A p..B p, F p x) L p₀ := by
  simpa only [integral_eq_affinePullback] using h

end LogConcaveExtremum.ParametricInterval

/-! ## Flattened source: `lean_i/AlgebraicKKTExtraction.lean` -/



namespace LogConcaveClaimI

/-!
This file contains only the finite-dimensional algebra that follows the
Lagrange-multiplier theorem.  The coordinates of `v : Fin 6 -> R` are, in
order, the left endpoint, the right endpoint, the additive constant, the
linear coefficient, the size of the kink, and the location of the kink.

`L j` and `R j` denote the order-`j` moments on the two sides of the kink.
The nonzero numbers `rhoA` and `rhoB` are the endpoint densities with the
sign dictated by differentiation of an integral with moving endpoints.
-/

def momentVariation (L R : ℕ → ℝ) (A B m delta rhoA rhoB : ℝ)
    (v : Fin 6 → ℝ) (k : Fin 3) : ℝ :=
  rhoA * v 0 * A ^ k.val + rhoB * v 1 * B ^ k.val +
    v 2 * (L k.val + R k.val) +
    v 3 * (L (k.val + 1) + R (k.val + 1)) -
    v 4 * (R (k.val + 1) - m * R k.val) +
    v 5 * delta * R k.val

def objectiveVariation
    (HL0 HL1 HR0 HR1 hA hB m delta rhoA rhoB : ℝ)
    (v : Fin 6 → ℝ) : ℝ :=
  rhoA * v 0 * hA + rhoB * v 1 * hB +
    v 2 * (HL0 + HR0) + v 3 * (HL1 + HR1) -
    v 4 * (HR1 - m * HR0) + v 5 * delta * HR0

/-!
The theorem is deliberately stated after the multiplier has been normalized:
the coefficient of the objective derivative is one.  Surjectivity of the
moment derivative is what rules out an abnormal multiplier and supplies this
normalization.
-/
theorem residual_equations_of_normalized_factorization
    {L R : ℕ → ℝ} {A B m delta rhoA rhoB : ℝ}
    {HL0 HL1 HR0 HR1 hA hB lambda₀ lambda₁ lambda₂ : ℝ}
    (hdelta : delta ≠ 0) (hrhoA : rhoA ≠ 0) (hrhoB : rhoB ≠ 0)
    (hfactor : ∀ v : Fin 6 → ℝ,
      objectiveVariation HL0 HL1 HR0 HR1 hA hB m delta rhoA rhoB v =
        lambda₀ * momentVariation L R A B m delta rhoA rhoB v 0 +
        lambda₁ * momentVariation L R A B m delta rhoA rhoB v 1 +
        lambda₂ * momentVariation L R A B m delta rhoA rhoB v 2) :
    HL0 = lambda₀ * L 0 + lambda₁ * L 1 + lambda₂ * L 2 ∧
    HL1 = lambda₀ * L 1 + lambda₁ * L 2 + lambda₂ * L 3 ∧
    HR0 = lambda₀ * R 0 + lambda₁ * R 1 + lambda₂ * R 2 ∧
    HR1 = lambda₀ * R 1 + lambda₁ * R 2 + lambda₂ * R 3 ∧
    hA = lambda₀ + lambda₁ * A + lambda₂ * A ^ 2 ∧
    hB = lambda₀ + lambda₁ * B + lambda₂ * B ^ 2 := by
  have hAeq := hfactor (Pi.single (M := fun _ : Fin 6 ↦ ℝ) (0 : Fin 6) 1)
  have hBeq := hfactor (Pi.single (M := fun _ : Fin 6 ↦ ℝ) (1 : Fin 6) 1)
  have hceq := hfactor (Pi.single (M := fun _ : Fin 6 ↦ ℝ) (2 : Fin 6) 1)
  have hbeq := hfactor (Pi.single (M := fun _ : Fin 6 ↦ ℝ) (3 : Fin 6) 1)
  have hdeq := hfactor (Pi.single (M := fun _ : Fin 6 ↦ ℝ) (4 : Fin 6) 1)
  have hmeq := hfactor (Pi.single (M := fun _ : Fin 6 ↦ ℝ) (5 : Fin 6) 1)
  norm_num [objectiveVariation, momentVariation] at hAeq hBeq hceq hbeq hdeq hmeq
  simp at hAeq hBeq hceq hbeq hdeq hmeq
  have hR0 : HR0 = lambda₀ * R 0 + lambda₁ * R 1 + lambda₂ * R 2 := by
    apply mul_left_cancel₀ hdelta
    nlinarith [hmeq]
  have hR1 : HR1 = lambda₀ * R 1 + lambda₁ * R 2 + lambda₂ * R 3 := by
    rw [hR0] at hdeq
    nlinarith [hdeq]
  have hL0 : HL0 = lambda₀ * L 0 + lambda₁ * L 1 + lambda₂ * L 2 := by
    rw [hR0] at hceq
    nlinarith [hceq]
  have hL1 : HL1 = lambda₀ * L 1 + lambda₁ * L 2 + lambda₂ * L 3 := by
    rw [hR1] at hbeq
    nlinarith [hbeq]
  have hAres : hA = lambda₀ + lambda₁ * A + lambda₂ * A ^ 2 := by
    apply mul_left_cancel₀ hrhoA
    nlinarith [hAeq]
  have hBres : hB = lambda₀ + lambda₁ * B + lambda₂ * B ^ 2 := by
    apply mul_left_cancel₀ hrhoB
    nlinarith [hBeq]
  exact ⟨hL0, hL1, hR0, hR1, hAres, hBres⟩

/-! The half-line versions are useful when only one endpoint is finite. -/

def momentVariationLeft (L R : ℕ → ℝ) (A m delta rhoA : ℝ)
    (v : Fin 5 → ℝ) (k : Fin 3) : ℝ :=
  rhoA * v 0 * A ^ k.val + v 1 * (L k.val + R k.val) +
    v 2 * (L (k.val + 1) + R (k.val + 1)) -
    v 3 * (R (k.val + 1) - m * R k.val) + v 4 * delta * R k.val

def objectiveVariationLeft
    (HL0 HL1 HR0 HR1 hA m delta rhoA : ℝ) (v : Fin 5 → ℝ) : ℝ :=
  rhoA * v 0 * hA + v 1 * (HL0 + HR0) + v 2 * (HL1 + HR1) -
    v 3 * (HR1 - m * HR0) + v 4 * delta * HR0

theorem residual_equations_of_normalized_factorization_left
    {L R : ℕ → ℝ} {A m delta rhoA : ℝ}
    {HL0 HL1 HR0 HR1 hA lambda₀ lambda₁ lambda₂ : ℝ}
    (hdelta : delta ≠ 0) (hrhoA : rhoA ≠ 0)
    (hfactor : ∀ v : Fin 5 → ℝ,
      objectiveVariationLeft HL0 HL1 HR0 HR1 hA m delta rhoA v =
        lambda₀ * momentVariationLeft L R A m delta rhoA v 0 +
        lambda₁ * momentVariationLeft L R A m delta rhoA v 1 +
        lambda₂ * momentVariationLeft L R A m delta rhoA v 2) :
    HL0 = lambda₀ * L 0 + lambda₁ * L 1 + lambda₂ * L 2 ∧
    HL1 = lambda₀ * L 1 + lambda₁ * L 2 + lambda₂ * L 3 ∧
    HR0 = lambda₀ * R 0 + lambda₁ * R 1 + lambda₂ * R 2 ∧
    HR1 = lambda₀ * R 1 + lambda₁ * R 2 + lambda₂ * R 3 ∧
    hA = lambda₀ + lambda₁ * A + lambda₂ * A ^ 2 := by
  have hAeq := hfactor (Pi.single (M := fun _ : Fin 5 ↦ ℝ) (0 : Fin 5) 1)
  have hceq := hfactor (Pi.single (M := fun _ : Fin 5 ↦ ℝ) (1 : Fin 5) 1)
  have hbeq := hfactor (Pi.single (M := fun _ : Fin 5 ↦ ℝ) (2 : Fin 5) 1)
  have hdeq := hfactor (Pi.single (M := fun _ : Fin 5 ↦ ℝ) (3 : Fin 5) 1)
  have hmeq := hfactor (Pi.single (M := fun _ : Fin 5 ↦ ℝ) (4 : Fin 5) 1)
  norm_num [objectiveVariationLeft, momentVariationLeft] at hAeq hceq hbeq hdeq hmeq
  simp at hAeq hceq hbeq hdeq hmeq
  have hR0 : HR0 = lambda₀ * R 0 + lambda₁ * R 1 + lambda₂ * R 2 := by
    apply mul_left_cancel₀ hdelta
    nlinarith [hmeq]
  have hR1 : HR1 = lambda₀ * R 1 + lambda₁ * R 2 + lambda₂ * R 3 := by
    rw [hR0] at hdeq
    nlinarith [hdeq]
  have hL0 : HL0 = lambda₀ * L 0 + lambda₁ * L 1 + lambda₂ * L 2 := by
    rw [hR0] at hceq
    nlinarith [hceq]
  have hL1 : HL1 = lambda₀ * L 1 + lambda₁ * L 2 + lambda₂ * L 3 := by
    rw [hR1] at hbeq
    nlinarith [hbeq]
  have hAres : hA = lambda₀ + lambda₁ * A + lambda₂ * A ^ 2 := by
    apply mul_left_cancel₀ hrhoA
    nlinarith [hAeq]
  exact ⟨hL0, hL1, hR0, hR1, hAres⟩

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/MomentRank.lean` -/



namespace LogConcaveClaimI

open Function

def momentJacobian (L R : ℕ → ℝ) (m delta : ℝ) :
    (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v k :=
    v 0 * (L k.val + R k.val) +
    v 1 * (L (k.val + 1) + R (k.val + 1)) -
    v 2 * (R (k.val + 1) - m * R k.val) +
    v 3 * delta * R k.val
  map_add' x y := by ext k; simp; ring
  map_smul' c x := by ext k; simp; ring

private lemma dual_fin3_expand (Lambda : Module.Dual ℝ (Fin 3 → ℝ)) (y : Fin 3 → ℝ) :
    Lambda y =
      y 0 * Lambda (Pi.single 0 1) +
      y 1 * Lambda (Pi.single 1 1) +
      y 2 * Lambda (Pi.single 2 1) := by
  have hy : y = y 0 • Pi.single (0 : Fin 3) 1 +
      y 1 • Pi.single (1 : Fin 3) 1 + y 2 • Pi.single (2 : Fin 3) 1 := by
    ext i
    fin_cases i <;> simp
  rw [hy, map_add, map_add, map_smul, map_smul, map_smul]
  simp [mul_comm]

/-! The rank calculation used by the genuine-kink KKT argument.  `L j` and `R j`
stand for the moments of order `j` on the two sides of the kink.  The sole analytic
hypothesis says that no nonzero quadratic can have its first two moments vanish on
both sides; the weighted two-zero lemma proves this hypothesis. -/
theorem momentJacobian_surjective
    {L R : ℕ → ℝ} {m delta : ℝ} (hdelta : delta ≠ 0)
    (hpoly : ∀ a b c : ℝ,
      a * L 0 + b * L 1 + c * L 2 = 0 →
      a * L 1 + b * L 2 + c * L 3 = 0 →
      a * R 0 + b * R 1 + c * R 2 = 0 →
      a * R 1 + b * R 2 + c * R 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    Function.Surjective (momentJacobian L R m delta) := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro Lambda hLambda
  rw [LinearMap.mem_ker] at hLambda
  have hann : ∀ v, Lambda (momentJacobian L R m delta v) = 0 := by
    intro v
    have h := LinearMap.congr_fun hLambda v
    simpa using h
  let a := Lambda (Pi.single (0 : Fin 3) 1)
  let b := Lambda (Pi.single (1 : Fin 3) 1)
  let c := Lambda (Pi.single (2 : Fin 3) 1)
  have hcdir := hann (Pi.single (M := fun _ : Fin 4 ↦ ℝ) (0 : Fin 4) 1)
  have hbdir := hann (Pi.single (M := fun _ : Fin 4 ↦ ℝ) (1 : Fin 4) 1)
  have hddir := hann (Pi.single (M := fun _ : Fin 4 ↦ ℝ) (2 : Fin 4) 1)
  have hmdir := hann (Pi.single (M := fun _ : Fin 4 ↦ ℝ) (3 : Fin 4) 1)
  rw [dual_fin3_expand] at hcdir hbdir hddir hmdir
  norm_num [momentJacobian] at hcdir hbdir hddir hmdir
  simp at hcdir hbdir hddir hmdir
  ring_nf at hcdir hbdir hddir hmdir
  have hcdir' : a * (L 0 + R 0) + b * (L 1 + R 1) + c * (L 2 + R 2) = 0 := by
    dsimp [a, b, c]
    nlinarith [hcdir]
  have hbdir' : a * (L 1 + R 1) + b * (L 2 + R 2) + c * (L 3 + R 3) = 0 := by
    dsimp [a, b, c]
    nlinarith [hbdir]
  have hddir' : -(a * (R 1 - m * R 0) + b * (R 2 - m * R 1) +
      c * (R 3 - m * R 2)) = 0 := by
    dsimp [a, b, c]
    nlinarith [hddir]
  have hmdir' : delta * (a * R 0 + b * R 1 + c * R 2) = 0 := by
    dsimp [a, b, c]
    nlinarith [hmdir]
  have hR0 : a * R 0 + b * R 1 + c * R 2 = 0 := by
    exact (mul_eq_zero.mp hmdir').resolve_left hdelta
  have hR1 : a * R 1 + b * R 2 + c * R 3 = 0 := by
    linear_combination -hddir' + m * hR0
  have hL0 : a * L 0 + b * L 1 + c * L 2 = 0 := by
    nlinarith [hcdir']
  have hL1 : a * L 1 + b * L 2 + c * L 3 = 0 := by
    nlinarith [hbdir']
  obtain ⟨ha, hb, hc⟩ := hpoly a b c hL0 hL1 hR0 hR1
  apply LinearMap.ext
  intro y
  rw [dual_fin3_expand]
  simp [a, b, c, ha, hb, hc]

def momentJacobianCLM (L R : ℕ → ℝ) (m delta : ℝ) :
    (Fin 4 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (momentJacobian L R m delta).toContinuousLinearMap

lemma momentJacobianCLM_surjective
    {L R : ℕ → ℝ} {m delta : ℝ} (hdelta : delta ≠ 0)
    (hpoly : ∀ a b c : ℝ,
      a * L 0 + b * L 1 + c * L 2 = 0 →
      a * L 1 + b * L 2 + c * L 3 = 0 →
      a * R 0 + b * R 1 + c * R 2 = 0 →
      a * R 1 + b * R 2 + c * R 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    Function.Surjective (momentJacobianCLM L R m delta) :=
  momentJacobian_surjective hdelta hpoly

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/NormalizedLagrange.lean` -/



open Set

namespace LogConcaveClaimI

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-! A normalized form of Mathlib's Lagrange-multiplier theorem.  Surjectivity of the
constraint derivative rules out an abnormal multiplier. -/
theorem IsLocalExtrOn.exists_normalized_lagrange_multiplier
    {f : E → F} {phi : E → ℝ} {x₀ : E}
    {f' : E →L[ℝ] F} {phi' : StrongDual ℝ E}
    (hextr : IsLocalExtrOn phi {x | f x = f x₀} x₀)
    (hf : HasStrictFDerivAt f f' x₀) (hphi : HasStrictFDerivAt phi phi' x₀)
    (hsurj : Function.Surjective f') :
    ∃ Lambda : Module.Dual ℝ F, ∀ v, phi' v = Lambda (f' v) := by
  obtain ⟨Lambda, Lambda₀, hne, hrel⟩ :=
    hextr.exists_linear_map_of_hasStrictFDerivAt hf hphi
  have hLambda₀ : Lambda₀ ≠ 0 := by
    intro hzero
    have hLambda : Lambda = 0 := by
      ext y
      obtain ⟨v, rfl⟩ := hsurj y
      have h := hrel v
      simp [hzero] at h
      exact h
    exact hne (by simp [hLambda, hzero])
  refine ⟨(-Lambda₀⁻¹) • Lambda, fun v ↦ ?_⟩
  have h := hrel v
  simp only [smul_eq_mul] at h ⊢
  change phi' v = (-Lambda₀⁻¹) * Lambda (f' v)
  rw [show (-Lambda₀⁻¹) * Lambda (f' v) = Lambda₀⁻¹ * (-Lambda (f' v)) by ring]
  apply (eq_inv_mul_iff_mul_eq₀ hLambda₀).2
  linarith

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/KKTAssembly.lean` -/



namespace LogConcaveClaimI

def twoEndpointMomentJacobian
    (L R : ℕ → ℝ) (A B m delta rhoA rhoB : ℝ) :
    (Fin 6 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v k := momentVariation L R A B m delta rhoA rhoB v k
  map_add' v w := by ext k; simp [momentVariation]; ring
  map_smul' c v := by ext k; simp [momentVariation]; ring

def twoEndpointMomentJacobianCLM
    (L R : ℕ → ℝ) (A B m delta rhoA rhoB : ℝ) :
    (Fin 6 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (twoEndpointMomentJacobian L R A B m delta rhoA rhoB).toContinuousLinearMap

def twoEndpointObjectiveJacobian
    (HL0 HL1 HR0 HR1 hA hB m delta rhoA rhoB : ℝ) :
    (Fin 6 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := objectiveVariation HL0 HL1 HR0 HR1 hA hB m delta rhoA rhoB v
  map_add' v w := by simp [objectiveVariation]; ring
  map_smul' c v := by simp [objectiveVariation]; ring

def twoEndpointObjectiveJacobianCLM
    (HL0 HL1 HR0 HR1 hA hB m delta rhoA rhoB : ℝ) :
    (Fin 6 → ℝ) →L[ℝ] ℝ :=
  (twoEndpointObjectiveJacobian HL0 HL1 HR0 HR1 hA hB m delta rhoA rhoB).toContinuousLinearMap

lemma twoEndpointMomentJacobian_surjective
    {L R : ℕ → ℝ} {A B m delta rhoA rhoB : ℝ}
    (hdelta : delta ≠ 0)
    (hpoly : ∀ a b c : ℝ,
      a * L 0 + b * L 1 + c * L 2 = 0 →
      a * L 1 + b * L 2 + c * L 3 = 0 →
      a * R 0 + b * R 1 + c * R 2 = 0 →
      a * R 1 + b * R 2 + c * R 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    Function.Surjective
      (twoEndpointMomentJacobianCLM L R A B m delta rhoA rhoB) := by
  intro y
  obtain ⟨u, hu⟩ := momentJacobian_surjective (m := m) hdelta hpoly y
  let v : Fin 6 → ℝ := fun i ↦
    if i = 2 then u 0 else if i = 3 then u 1 else
    if i = 4 then u 2 else if i = 5 then u 3 else 0
  refine ⟨v, ?_⟩
  ext k
  have hk := congrFun hu k
  fin_cases k <;>
    norm_num [v, twoEndpointMomentJacobianCLM, twoEndpointMomentJacobian,
      momentVariation, momentJacobian] at hk ⊢ <;>
    simp at hk ⊢ <;>
    exact hk

lemma dual_fin_three (Lambda : Module.Dual ℝ (Fin 3 → ℝ)) (y : Fin 3 → ℝ) :
    Lambda y =
      y 0 * Lambda (Pi.single (M := fun _ : Fin 3 ↦ ℝ) 0 1) +
      y 1 * Lambda (Pi.single (M := fun _ : Fin 3 ↦ ℝ) 1 1) +
      y 2 * Lambda (Pi.single (M := fun _ : Fin 3 ↦ ℝ) 2 1) := by
  have hy : y =
      y 0 • Pi.single (M := fun _ : Fin 3 ↦ ℝ) 0 1 +
      y 1 • Pi.single (M := fun _ : Fin 3 ↦ ℝ) 1 1 +
      y 2 • Pi.single (M := fun _ : Fin 3 ↦ ℝ) 2 1 := by
    ext i
    fin_cases i <;> simp
  rw [hy, map_add, map_add, map_smul, map_smul, map_smul]
  simp [mul_comm]

/-!
This is the complete KKT-to-residual bridge for a compact genuine kink.
The analytic differentiation lemmas need only identify the two displayed
strict derivatives; everything after that point is finite-dimensional
algebra.
-/
theorem compact_KKT_residual_equations
    {M : (Fin 6 → ℝ) → (Fin 3 → ℝ)}
    {Phi : (Fin 6 → ℝ) → ℝ} {theta : Fin 6 → ℝ}
    {L R : ℕ → ℝ} {A B m delta rhoA rhoB : ℝ}
    {HL0 HL1 HR0 HR1 hA hB : ℝ}
    (hdelta : delta ≠ 0) (hrhoA : rhoA ≠ 0) (hrhoB : rhoB ≠ 0)
    (hpoly : ∀ a b c : ℝ,
      a * L 0 + b * L 1 + c * L 2 = 0 →
      a * L 1 + b * L 2 + c * L 3 = 0 →
      a * R 0 + b * R 1 + c * R 2 = 0 →
      a * R 1 + b * R 2 + c * R 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0)
    (hmax : IsLocalExtrOn Phi {x | M x = M theta} theta)
    (hM : HasStrictFDerivAt M
      (twoEndpointMomentJacobianCLM L R A B m delta rhoA rhoB) theta)
    (hPhi : HasStrictFDerivAt Phi
      (twoEndpointObjectiveJacobianCLM
        HL0 HL1 HR0 HR1 hA hB m delta rhoA rhoB) theta) :
    ∃ lambda₀ lambda₁ lambda₂ : ℝ,
      HL0 = lambda₀ * L 0 + lambda₁ * L 1 + lambda₂ * L 2 ∧
      HL1 = lambda₀ * L 1 + lambda₁ * L 2 + lambda₂ * L 3 ∧
      HR0 = lambda₀ * R 0 + lambda₁ * R 1 + lambda₂ * R 2 ∧
      HR1 = lambda₀ * R 1 + lambda₁ * R 2 + lambda₂ * R 3 ∧
      hA = lambda₀ + lambda₁ * A + lambda₂ * A ^ 2 ∧
      hB = lambda₀ + lambda₁ * B + lambda₂ * B ^ 2 := by
  have hsurj := twoEndpointMomentJacobian_surjective
    (A := A) (B := B) (m := m) (rhoA := rhoA) (rhoB := rhoB) hdelta hpoly
  obtain ⟨Lambda, hLambda⟩ :=
    LogConcaveClaimI.IsLocalExtrOn.exists_normalized_lagrange_multiplier
      hmax hM hPhi hsurj
  let lambda₀ := Lambda (Pi.single (M := fun _ : Fin 3 ↦ ℝ) 0 1)
  let lambda₁ := Lambda (Pi.single (M := fun _ : Fin 3 ↦ ℝ) 1 1)
  let lambda₂ := Lambda (Pi.single (M := fun _ : Fin 3 ↦ ℝ) 2 1)
  have hfactor : ∀ v : Fin 6 → ℝ,
      objectiveVariation HL0 HL1 HR0 HR1 hA hB m delta rhoA rhoB v =
        lambda₀ * momentVariation L R A B m delta rhoA rhoB v 0 +
        lambda₁ * momentVariation L R A B m delta rhoA rhoB v 1 +
        lambda₂ * momentVariation L R A B m delta rhoA rhoB v 2 := by
    intro v
    have h := hLambda v
    rw [dual_fin_three] at h
    simpa [twoEndpointObjectiveJacobianCLM, twoEndpointObjectiveJacobian,
      twoEndpointMomentJacobianCLM, twoEndpointMomentJacobian,
      lambda₀, lambda₁, lambda₂, mul_comm] using h
  exact ⟨lambda₀, lambda₁, lambda₂,
    residual_equations_of_normalized_factorization
      hdelta hrhoA hrhoB hfactor⟩

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/CompactParametric.lean` -/



open Real Set MeasureTheory intervalIntegral
open scoped Topology Interval

namespace LogConcaveClaimI

abbrev CompactParam := Fin 6 → ℝ

def compactCoord (i : Fin 6) : CompactParam →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

@[simp] lemma compactCoord_apply (i : Fin 6) (p : CompactParam) :
    compactCoord i p = p i := rfl

def leftExponent (p : CompactParam) (x : ℝ) : ℝ :=
  p 2 + p 3 * x

def rightExponent (p : CompactParam) (x : ℝ) : ℝ :=
  p 2 + p 3 * x - p 4 * (x - p 5)

def leftIntegrand (q : ℝ → ℝ) (p : CompactParam) (x : ℝ) : ℝ :=
  q x * exp (leftExponent p x)

def rightIntegrand (q : ℝ → ℝ) (p : CompactParam) (x : ℝ) : ℝ :=
  q x * exp (rightExponent p x)

def leftIntegrandFDeriv (q : ℝ → ℝ) (p : CompactParam) (x : ℝ) :
    CompactParam →L[ℝ] ℝ :=
  (compactCoord 2).smulRight (leftIntegrand q p x) +
    (compactCoord 3).smulRight (x * leftIntegrand q p x)

def rightIntegrandFDeriv (q : ℝ → ℝ) (p : CompactParam) (x : ℝ) :
    CompactParam →L[ℝ] ℝ :=
  (compactCoord 2).smulRight (rightIntegrand q p x) +
    (compactCoord 3).smulRight (x * rightIntegrand q p x) -
    (compactCoord 4).smulRight ((x - p 5) * rightIntegrand q p x) +
    (compactCoord 5).smulRight (p 4 * rightIntegrand q p x)

lemma continuous_uncurry_leftIntegrand {q : ℝ → ℝ} (hq : Continuous q) :
    Continuous (Function.uncurry (leftIntegrand q)) := by
  unfold leftIntegrand leftExponent
  fun_prop

lemma continuous_uncurry_rightIntegrand {q : ℝ → ℝ} (hq : Continuous q) :
    Continuous (Function.uncurry (rightIntegrand q)) := by
  unfold rightIntegrand rightExponent
  fun_prop

lemma continuous_uncurry_leftIntegrandFDeriv {q : ℝ → ℝ} (hq : Continuous q) :
    Continuous (Function.uncurry (leftIntegrandFDeriv q)) := by
  unfold leftIntegrandFDeriv leftIntegrand leftExponent compactCoord
  fun_prop

lemma continuous_uncurry_rightIntegrandFDeriv {q : ℝ → ℝ} (hq : Continuous q) :
    Continuous (Function.uncurry (rightIntegrandFDeriv q)) := by
  unfold rightIntegrandFDeriv rightIntegrand rightExponent compactCoord
  fun_prop

lemma hasFDerivAt_leftIntegrand (q : ℝ → ℝ) (p : CompactParam) (x : ℝ) :
    HasFDerivAt (fun u ↦ leftIntegrand q u x)
      (leftIntegrandFDeriv q p x) p := by
  have hE : HasFDerivAt (fun u : CompactParam ↦ leftExponent u x)
      (compactCoord 2 + x • compactCoord 3) p := by
    unfold leftExponent
    fun_prop
  have h := hE.exp.const_mul (q x)
  apply h.congr_fderiv
  ext v
  simp [leftIntegrandFDeriv, leftIntegrand, compactCoord]
  ring

lemma hasFDerivAt_rightIntegrand (q : ℝ → ℝ) (p : CompactParam) (x : ℝ) :
    HasFDerivAt (fun u ↦ rightIntegrand q u x)
      (rightIntegrandFDeriv q p x) p := by
  have hE : HasFDerivAt (fun u : CompactParam ↦ rightExponent u x)
      (compactCoord 2 + x • compactCoord 3 -
        (x - p 5) • compactCoord 4 + p 4 • compactCoord 5) p := by
    have hraw := ((compactCoord 2).hasFDerivAt.add
      ((compactCoord 3).hasFDerivAt.mul_const x)).sub
        ((compactCoord 4).hasFDerivAt.mul
          ((hasFDerivAt_const x p).sub (compactCoord 5).hasFDerivAt))
    have hsame : HasFDerivAt (fun u : CompactParam ↦ rightExponent u x)
        _ p := hraw.congr_of_eventuallyEq (by
      filter_upwards [] with u
      rfl)
    apply hsame.congr_fderiv
    ext v
    simp [compactCoord]
    ring
  have h := hE.exp.const_mul (q x)
  apply h.congr_fderiv
  ext v
  simp [rightIntegrandFDeriv, rightIntegrand, compactCoord]
  ring

def leftIntegral (q : ℝ → ℝ) (p : CompactParam) : ℝ :=
  ∫ x in p 0..p 5, leftIntegrand q p x

def rightIntegral (q : ℝ → ℝ) (p : CompactParam) : ℝ :=
  ∫ x in p 5..p 1, rightIntegrand q p x

def compactIntegral (q : ℝ → ℝ) (p : CompactParam) : ℝ :=
  leftIntegral q p + rightIntegral q p

def leftIntegralFDerivRaw (q : ℝ → ℝ) (p : CompactParam) :
    CompactParam →L[ℝ] ℝ :=
  (((∫ x in p 0..p 5, leftIntegrandFDeriv q p x).coprod
      (LogConcaveExtremum.ParametricInterval.endpointFDeriv
        (leftIntegrand q) p (p 0) (p 5))) ∘L
    ((ContinuousLinearMap.id ℝ CompactParam).prod
      ((compactCoord 0).prod (compactCoord 5))))

def rightIntegralFDerivRaw (q : ℝ → ℝ) (p : CompactParam) :
    CompactParam →L[ℝ] ℝ :=
  (((∫ x in p 5..p 1, rightIntegrandFDeriv q p x).coprod
      (LogConcaveExtremum.ParametricInterval.endpointFDeriv
        (rightIntegrand q) p (p 5) (p 1))) ∘L
    ((ContinuousLinearMap.id ℝ CompactParam).prod
      ((compactCoord 5).prod (compactCoord 1))))

lemma hasStrictFDerivAt_leftIntegral {q : ℝ → ℝ} (hq : Continuous q)
    (p : CompactParam) :
    HasStrictFDerivAt (leftIntegral q) (leftIntegralFDerivRaw q p) p := by
  exact LogConcaveExtremum.ParametricInterval.hasStrictFDerivAt_movingIntervalIntegral_of_continuous
      (F := leftIntegrand q) (F' := leftIntegrandFDeriv q)
      (A := fun u : CompactParam ↦ u 0) (B := fun u : CompactParam ↦ u 5)
      (p₀ := p) (A' := compactCoord 0) (B' := compactCoord 5)
      (continuous_uncurry_leftIntegrand hq)
      (continuous_uncurry_leftIntegrandFDeriv hq)
      (hasFDerivAt_leftIntegrand q)
      (compactCoord 0).hasStrictFDerivAt
      (compactCoord 5).hasStrictFDerivAt

lemma hasStrictFDerivAt_rightIntegral {q : ℝ → ℝ} (hq : Continuous q)
    (p : CompactParam) :
    HasStrictFDerivAt (rightIntegral q) (rightIntegralFDerivRaw q p) p := by
  exact LogConcaveExtremum.ParametricInterval.hasStrictFDerivAt_movingIntervalIntegral_of_continuous
      (F := rightIntegrand q) (F' := rightIntegrandFDeriv q)
      (A := fun u : CompactParam ↦ u 5) (B := fun u : CompactParam ↦ u 1)
      (p₀ := p) (A' := compactCoord 5) (B' := compactCoord 1)
      (continuous_uncurry_rightIntegrand hq)
      (continuous_uncurry_rightIntegrandFDeriv hq)
      (hasFDerivAt_rightIntegrand q)
      (compactCoord 5).hasStrictFDerivAt
      (compactCoord 1).hasStrictFDerivAt

lemma hasStrictFDerivAt_compactIntegral_raw {q : ℝ → ℝ} (hq : Continuous q)
    (p : CompactParam) :
    HasStrictFDerivAt (compactIntegral q)
      (leftIntegralFDerivRaw q p + rightIntegralFDerivRaw q p) p := by
  exact (hasStrictFDerivAt_leftIntegral hq p).add
    (hasStrictFDerivAt_rightIntegral hq p)

def compactIntegralFDerivKKT (q : ℝ → ℝ) (p : CompactParam) :
    CompactParam →L[ℝ] ℝ :=
  twoEndpointObjectiveJacobianCLM
    (leftIntegral q p) (leftIntegral (fun x ↦ x * q x) p)
    (rightIntegral q p) (rightIntegral (fun x ↦ x * q x) p)
    (q (p 0)) (q (p 1)) (p 5) (p 4)
    (-exp (leftExponent p (p 0))) (exp (rightExponent p (p 1)))

lemma compactIntegralFDerivRaw_eq_KKT {q : ℝ → ℝ} (hq : Continuous q)
    (p : CompactParam) :
    leftIntegralFDerivRaw q p + rightIntegralFDerivRaw q p =
      compactIntegralFDerivKKT q p := by
  apply ContinuousLinearMap.ext
  intro v
  have hLi : IntervalIntegrable (leftIntegrandFDeriv q p) volume (p 0) (p 5) :=
    ((continuous_uncurry_leftIntegrandFDeriv hq).uncurry_left p).intervalIntegrable _ _
  have hRi : IntervalIntegrable (rightIntegrandFDeriv q p) volume (p 5) (p 1) :=
    ((continuous_uncurry_rightIntegrandFDeriv hq).uncurry_left p).intervalIntegrable _ _
  have hLc : Continuous (leftIntegrand q p) :=
    (continuous_uncurry_leftIntegrand hq).uncurry_left p
  have hRc : Continuous (rightIntegrand q p) :=
    (continuous_uncurry_rightIntegrand hq).uncurry_left p
  have hL0 : IntervalIntegrable (leftIntegrand q p) volume (p 0) (p 5) :=
    hLc.intervalIntegrable _ _
  have hL1 : IntervalIntegrable
      (fun x ↦ x * leftIntegrand q p x) volume (p 0) (p 5) :=
    (continuous_id.mul hLc).intervalIntegrable _ _
  have hR0 : IntervalIntegrable (rightIntegrand q p) volume (p 5) (p 1) :=
    hRc.intervalIntegrable _ _
  have hR1 : IntervalIntegrable
      (fun x ↦ x * rightIntegrand q p x) volume (p 5) (p 1) :=
    (continuous_id.mul hRc).intervalIntegrable _ _
  have hRxm : IntervalIntegrable
      (fun x ↦ (x - p 5) * rightIntegrand q p x) volume (p 5) (p 1) :=
    ((continuous_id.sub continuous_const).mul hRc).intervalIntegrable _ _
  have hLweighted :
      (∫ x in p 0..p 5, x * leftIntegrand q p x) =
        leftIntegral (fun x ↦ x * q x) p := by
    unfold leftIntegral leftIntegrand
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  have hRweighted :
      (∫ x in p 5..p 1, x * rightIntegrand q p x) =
        rightIntegral (fun x ↦ x * q x) p := by
    unfold rightIntegral rightIntegrand
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  have hRxmIntegral :
      (∫ x in p 5..p 1, (x - p 5) * rightIntegrand q p x) =
        rightIntegral (fun x ↦ x * q x) p - p 5 * rightIntegral q p := by
    calc
      (∫ x in p 5..p 1, (x - p 5) * rightIntegrand q p x) =
          ∫ x in p 5..p 1,
            x * rightIntegrand q p x - p 5 * rightIntegrand q p x := by
              apply intervalIntegral.integral_congr
              intro x hx
              ring
      _ = (∫ x in p 5..p 1, x * rightIntegrand q p x) -
          ∫ x in p 5..p 1, p 5 * rightIntegrand q p x :=
            intervalIntegral.integral_sub hR1 (hR0.const_mul (p 5))
      _ = rightIntegral (fun x ↦ x * q x) p - p 5 * rightIntegral q p := by
            rw [intervalIntegral.integral_const_mul, hRweighted]
            rfl
  have hLint :
      (∫ x in p 0..p 5,
        v 2 * leftIntegrand q p x + v 3 * (x * leftIntegrand q p x)) =
        v 2 * leftIntegral q p +
          v 3 * leftIntegral (fun x ↦ x * q x) p := by
    rw [intervalIntegral.integral_add (hL0.const_mul (v 2))
      (hL1.const_mul (v 3)), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hLweighted]
    rfl
  have hRint :
      (∫ x in p 5..p 1,
        v 2 * rightIntegrand q p x + v 3 * (x * rightIntegrand q p x) -
          v 4 * ((x - p 5) * rightIntegrand q p x) +
          v 5 * (p 4 * rightIntegrand q p x)) =
        v 2 * rightIntegral q p +
          v 3 * rightIntegral (fun x ↦ x * q x) p -
          v 4 * (rightIntegral (fun x ↦ x * q x) p - p 5 * rightIntegral q p) +
          v 5 * (p 4 * rightIntegral q p) := by
    rw [intervalIntegral.integral_add
      (((hR0.const_mul (v 2)).add (hR1.const_mul (v 3))).sub
        (hRxm.const_mul (v 4)))
      ((hR0.const_mul (p 4)).const_mul (v 5)),
      intervalIntegral.integral_sub
        ((hR0.const_mul (v 2)).add (hR1.const_mul (v 3)))
        (hRxm.const_mul (v 4)),
      intervalIntegral.integral_add (hR0.const_mul (v 2))
        (hR1.const_mul (v 3))]
    simp only [intervalIntegral.integral_const_mul]
    rw [hRweighted, hRxmIntegral]
    simp only [rightIntegral]
  have hm : leftIntegrand q p (p 5) = rightIntegrand q p (p 5) := by
    simp only [leftIntegrand, rightIntegrand, leftExponent, rightExponent]
    ring_nf
  simp only [ContinuousLinearMap.add_apply, leftIntegralFDerivRaw,
    rightIntegralFDerivRaw, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coprod_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply]
  rw [ContinuousLinearMap.intervalIntegral_apply hLi v,
    ContinuousLinearMap.intervalIntegral_apply hRi v]
  simp [LogConcaveExtremum.ParametricInterval.endpointFDeriv,
    leftIntegrandFDeriv, rightIntegrandFDeriv, compactCoord]
  rw [hLint, hRint, hm]
  change _ = objectiveVariation
    (leftIntegral q p) (leftIntegral (fun x ↦ x * q x) p)
    (rightIntegral q p) (rightIntegral (fun x ↦ x * q x) p)
    (q (p 0)) (q (p 1)) (p 5) (p 4)
    (-exp (leftExponent p (p 0))) (exp (rightExponent p (p 1))) v
  simp only [objectiveVariation]
  simp only [leftIntegral, rightIntegral, leftIntegrand, rightIntegrand]
  ring

theorem hasStrictFDerivAt_compactIntegral {q : ℝ → ℝ} (hq : Continuous q)
    (p : CompactParam) :
    HasStrictFDerivAt (compactIntegral q) (compactIntegralFDerivKKT q p) p := by
  exact (hasStrictFDerivAt_compactIntegral_raw hq p).congr_fderiv
    (compactIntegralFDerivRaw_eq_KKT hq p)

def compactLeftMoment (p : CompactParam) (n : ℕ) : ℝ :=
  leftIntegral (fun x ↦ x ^ n) p

def compactRightMoment (p : CompactParam) (n : ℕ) : ℝ :=
  rightIntegral (fun x ↦ x ^ n) p

def compactMomentMap (p : CompactParam) (k : Fin 3) : ℝ :=
  compactIntegral (fun x ↦ x ^ k.val) p

def compactMomentFDerivPi (p : CompactParam) :
    CompactParam →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun k : Fin 3 ↦
    compactIntegralFDerivKKT (fun x ↦ x ^ k.val) p)

lemma leftIntegral_mul_pow (p : CompactParam) (n : ℕ) :
    leftIntegral (fun x ↦ x * x ^ n) p = compactLeftMoment p (n + 1) := by
  unfold compactLeftMoment leftIntegral leftIntegrand
  apply intervalIntegral.integral_congr
  intro x hx
  change (x * x ^ n) * exp (leftExponent p x) =
    x ^ (n + 1) * exp (leftExponent p x)
  rw [pow_succ]
  ring

lemma rightIntegral_mul_pow (p : CompactParam) (n : ℕ) :
    rightIntegral (fun x ↦ x * x ^ n) p = compactRightMoment p (n + 1) := by
  unfold compactRightMoment rightIntegral rightIntegrand
  apply intervalIntegral.integral_congr
  intro x hx
  change (x * x ^ n) * exp (rightExponent p x) =
    x ^ (n + 1) * exp (rightExponent p x)
  rw [pow_succ]
  ring

lemma hasStrictFDerivAt_compactMomentMap_pi (p : CompactParam) :
    HasStrictFDerivAt compactMomentMap (compactMomentFDerivPi p) p := by
  apply hasStrictFDerivAt_pi.mpr
  intro k
  exact hasStrictFDerivAt_compactIntegral (continuous_id.pow k.val) p

lemma compactMomentFDerivPi_eq_KKT (p : CompactParam) :
    compactMomentFDerivPi p =
      twoEndpointMomentJacobianCLM
        (compactLeftMoment p) (compactRightMoment p)
        (p 0) (p 1) (p 5) (p 4)
        (-exp (leftExponent p (p 0))) (exp (rightExponent p (p 1))) := by
  apply ContinuousLinearMap.ext
  intro v
  ext k
  simp only [compactMomentFDerivPi, ContinuousLinearMap.pi_apply]
  change objectiveVariation
      (compactLeftMoment p k.val)
      (leftIntegral (fun x ↦ x * x ^ k.val) p)
      (compactRightMoment p k.val)
      (rightIntegral (fun x ↦ x * x ^ k.val) p)
      ((p 0) ^ k.val) ((p 1) ^ k.val) (p 5) (p 4)
      (-exp (leftExponent p (p 0))) (exp (rightExponent p (p 1))) v =
    momentVariation (compactLeftMoment p) (compactRightMoment p)
      (p 0) (p 1) (p 5) (p 4)
      (-exp (leftExponent p (p 0))) (exp (rightExponent p (p 1))) v k
  rw [leftIntegral_mul_pow, rightIntegral_mul_pow]
  rfl

theorem hasStrictFDerivAt_compactMomentMap (p : CompactParam) :
    HasStrictFDerivAt compactMomentMap
      (twoEndpointMomentJacobianCLM
        (compactLeftMoment p) (compactRightMoment p)
        (p 0) (p 1) (p 5) (p 4)
        (-exp (leftExponent p (p 0))) (exp (rightExponent p (p 1)))) p := by
  exact (hasStrictFDerivAt_compactMomentMap_pi p).congr_fderiv
    (compactMomentFDerivPi_eq_KKT p)

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/AbstractMomentZeros.lean` -/



open Real Set

namespace LogConcaveClaimI

/-- The order-theoretic properties of a nonempty open interval, with finite or infinite
endpoints.  This formulation deliberately includes half-lines and the whole real line. -/
structure OpenOrderInterval (S : Set ℝ) : Prop where
  nonempty : S.Nonempty
  segment : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → uIcc x y ⊆ S
  exists_lt : ∀ ⦃x⦄, x ∈ S → ∃ y ∈ S, y < x
  exists_gt : ∀ ⦃x⦄, x ∈ S → ∃ y ∈ S, x < y

lemma openOrderInterval_Ioo {a b : ℝ} (hab : a < b) : OpenOrderInterval (Ioo a b) where
  nonempty := ⟨(a + b) / 2, by constructor <;> linarith⟩
  segment := by intro x hx y hy; exact ordConnected_Ioo.uIcc_subset hx hy
  exists_lt := by
    intro x hx
    exact ⟨(a + x) / 2, ⟨by linarith [hx.1], by linarith [hx.1, hx.2]⟩, by linarith [hx.1]⟩
  exists_gt := by
    intro x hx
    exact ⟨(x + b) / 2, ⟨by linarith [hx.1, hx.2], by linarith [hx.2]⟩, by linarith [hx.2]⟩

lemma openOrderInterval_Ioi (a : ℝ) : OpenOrderInterval (Ioi a) where
  nonempty := ⟨a + 1, by simp⟩
  segment := by intro x hx y hy; exact ordConnected_Ioi.uIcc_subset hx hy
  exists_lt := by
    intro x hx
    change a < x at hx
    exact ⟨(a + x) / 2, by change a < (a + x) / 2; linarith, by linarith⟩
  exists_gt := by
    intro x hx
    change a < x at hx
    exact ⟨x + 1, by change a < x + 1; linarith, by linarith⟩

lemma openOrderInterval_Iio (b : ℝ) : OpenOrderInterval (Iio b) where
  nonempty := ⟨b - 1, by simp⟩
  segment := by intro x hx y hy; exact ordConnected_Iio.uIcc_subset hx hy
  exists_lt := by
    intro x hx
    change x < b at hx
    exact ⟨x - 1, by change x - 1 < b; linarith, by linarith⟩
  exists_gt := by
    intro x hx
    change x < b at hx
    exact ⟨(x + b) / 2, by change (x + b) / 2 < b; linarith, by linarith⟩

lemma openOrderInterval_univ : OpenOrderInterval (univ : Set ℝ) where
  nonempty := ⟨0, mem_univ _⟩
  segment := by intro x hx y hy; exact subset_univ _
  exists_lt := fun {x} _ ↦ ⟨x - 1, mem_univ _, by linarith⟩
  exists_gt := fun {x} _ ↦ ⟨x + 1, mem_univ _, by linarith⟩

private lemma nonneg_on_of_pos_at_of_no_zero
    {S : Set ℝ} (hseg : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → uIcc x y ⊆ S)
    {r : ℝ → ℝ} (hr : ContinuousOn r S) {p : ℝ} (hp : p ∈ S) (hrp : 0 < r p)
    (hzero : ∀ z ∈ S, r z = 0 → False) : ∀ x ∈ S, 0 ≤ r x := by
  intro x hx
  by_contra hn
  have hrx : r x < 0 := lt_of_not_ge hn
  have hsub := hseg hx hp
  have hz : 0 ∈ r '' uIcc x p := by
    apply intermediate_value_uIcc (hr.mono hsub)
    rw [uIcc_of_le (hrx.trans hrp).le]
    exact ⟨hrx.le, hrp.le⟩
  obtain ⟨z, hzS, hrz⟩ := hz
  exact hzero z (hsub hzS) hrz

private lemma nonpos_on_of_neg_at_of_no_zero
    {S : Set ℝ} (hseg : ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → uIcc x y ⊆ S)
    {r : ℝ → ℝ} (hr : ContinuousOn r S) {p : ℝ} (hp : p ∈ S) (hrp : r p < 0)
    (hzero : ∀ z ∈ S, r z = 0 → False) : ∀ x ∈ S, r x ≤ 0 := by
  have h := nonneg_on_of_pos_at_of_no_zero hseg (r := fun x ↦ -r x) hr.neg hp
    (neg_pos.mpr hrp) (by
      intro z hz h
      exact hzero z hz (neg_eq_zero.mp h))
  intro x hx
  exact neg_nonneg.mp (h x hx)

/-- Abstract positivity property of integration against a strictly positive weight on `S`. -/
def StrictlyPositiveFunctionalOn (S : Set ℝ) (J : (ℝ → ℝ) → ℝ)
    (Admissible : (ℝ → ℝ) → Prop) : Prop :=
  ∀ q : ℝ → ℝ, Admissible q → ContinuousOn q S → (∀ x ∈ S, 0 ≤ q x) →
    (∃ x ∈ S, 0 < q x) → 0 < J q

/-! The unbounded-support version of the weighted sign-change lemma.  No endpoint occurs in
the statement: `S` may be a bounded open interval, a half-line, or all of `ℝ`. -/
theorem two_zeros_of_positive_functional
    {S : Set ℝ} (hS : OpenOrderInterval S) {J : (ℝ → ℝ) → ℝ}
    {Admissible : (ℝ → ℝ) → Prop}
    (hJpos : StrictlyPositiveFunctionalOn S J Admissible)
    (hJneg : ∀ q, J (fun x ↦ -q x) = -J q)
    (hAdm_neg : ∀ {q}, Admissible q → Admissible (fun x ↦ -q x))
    {r : ℝ → ℝ} (hr : ContinuousOn r S)
    (hAdm_r : Admissible r)
    (hAdm_s : ∀ c, Admissible (fun x ↦ (x - c) * r x))
    (h₀ : J r = 0) (h₁ : J (fun x ↦ x * r x) = 0)
    (hcombine : ∀ c, J (fun x ↦ (x - c) * r x) =
      J (fun x ↦ x * r x) - c * J r) :
    ∃ x₁ x₂, x₁ ∈ S ∧ x₂ ∈ S ∧ x₁ < x₂ ∧ r x₁ = 0 ∧ r x₂ = 0 := by
  have hneg_of_nonpos : ∀ (q : ℝ → ℝ), Admissible q → ContinuousOn q S →
      (∀ x ∈ S, q x ≤ 0) → (∃ x ∈ S, q x < 0) → J q < 0 := by
    intro q hqAdm hq hqnonpos hqstrict
    have hp := hJpos (fun x ↦ -q x) (hAdm_neg hqAdm) hq.neg
      (fun x hx ↦ neg_nonneg.mpr (hqnonpos x hx))
      (by obtain ⟨x, hx, hqx⟩ := hqstrict; exact ⟨x, hx, neg_pos.mpr hqx⟩)
    rw [hJneg] at hp
    linarith
  obtain ⟨p, hp⟩ := hS.nonempty
  have hexzero : ∃ c ∈ S, r c = 0 := by
    by_cases hrp : r p = 0
    · exact ⟨p, hp, hrp⟩
    by_contra hnone
    push Not at hnone
    rcases lt_or_gt_of_ne hrp with hrpneg | hrppos
    · have hall := nonpos_on_of_neg_at_of_no_zero hS.segment hr hp hrpneg hnone
      have hjneg := hneg_of_nonpos r hAdm_r hr hall ⟨p, hp, hrpneg⟩
      linarith
    · have hall := nonneg_on_of_pos_at_of_no_zero hS.segment hr hp hrppos hnone
      have hjpos := hJpos r hAdm_r hr hall ⟨p, hp, hrppos⟩
      linarith
  obtain ⟨c, hc, hrc⟩ := hexzero
  by_contra hnot
  have huniq : ∀ z ∈ S, r z = 0 → z = c := by
    intro z hz hrz
    by_contra hzc
    rcases lt_or_gt_of_ne hzc with hzc | hzc
    · exact hnot ⟨z, c, hz, hc, hzc, hrz, hrc⟩
    · exact hnot ⟨c, z, hc, hz, hzc, hrc, hrz⟩
  obtain ⟨p, hpS, hpc⟩ := hS.exists_lt hc
  obtain ⟨q, hqS, hcq⟩ := hS.exists_gt hc
  have hrp : r p ≠ 0 := fun h ↦ hpc.ne (huniq p hpS h)
  have hrq : r q ≠ 0 := fun h ↦ hcq.ne' (huniq q hqS h)
  let SL := S ∩ Iio c
  let SR := S ∩ Ioi c
  have hsegL : ∀ ⦃x⦄, x ∈ SL → ∀ ⦃y⦄, y ∈ SL → uIcc x y ⊆ SL := by
    intro x hx y hy z hz
    exact ⟨hS.segment hx.1 hy.1 hz,
      (ordConnected_Iio.uIcc_subset hx.2 hy.2) hz⟩
  have hsegR : ∀ ⦃x⦄, x ∈ SR → ∀ ⦃y⦄, y ∈ SR → uIcc x y ⊆ SR := by
    intro x hx y hy z hz
    exact ⟨hS.segment hx.1 hy.1 hz,
      (ordConnected_Ioi.uIcc_subset hx.2 hy.2) hz⟩
  have hzeroL : ∀ z ∈ SL, r z = 0 → False := by
    intro z hz hrz
    exact hz.2.ne (huniq z hz.1 hrz)
  have hzeroR : ∀ z ∈ SR, r z = 0 → False := by
    intro z hz hrz
    exact hz.2.ne' (huniq z hz.1 hrz)
  have hrL : ContinuousOn r SL := hr.mono inter_subset_left
  have hrR : ContinuousOn r SR := hr.mono inter_subset_left
  rcases lt_or_gt_of_ne hrp with hrpneg | hrppos <;>
    rcases lt_or_gt_of_ne hrq with hrqneg | hrqpos
  · have hL := nonpos_on_of_neg_at_of_no_zero hsegL hrL ⟨hpS, hpc⟩ hrpneg hzeroL
    have hR := nonpos_on_of_neg_at_of_no_zero hsegR hrR ⟨hqS, hcq⟩ hrqneg hzeroR
    have hall : ∀ x ∈ S, r x ≤ 0 := by
      intro x hx
      rcases lt_trichotomy x c with hxc | hxc | hxc
      · exact hL x ⟨hx, hxc⟩
      · subst x; simp [hrc]
      · exact hR x ⟨hx, hxc⟩
    have := hneg_of_nonpos r hAdm_r hr hall ⟨p, hpS, hrpneg⟩
    linarith
  · have hL := nonpos_on_of_neg_at_of_no_zero hsegL hrL ⟨hpS, hpc⟩ hrpneg hzeroL
    have hR := nonneg_on_of_pos_at_of_no_zero hsegR hrR ⟨hqS, hcq⟩ hrqpos hzeroR
    let s := fun x ↦ (x - c) * r x
    have hscont : ContinuousOn s S := (continuousOn_id.sub continuousOn_const).mul hr
    have hsnonneg : ∀ x ∈ S, 0 ≤ s x := by
      intro x hx
      rcases lt_trichotomy x c with hxc | hxc | hxc
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hxc.le) (hL x ⟨hx, hxc⟩)
      · subst x; simp [s]
      · exact mul_nonneg (sub_nonneg.mpr hxc.le) (hR x ⟨hx, hxc⟩)
    have hsp : 0 < s p := mul_pos_of_neg_of_neg (sub_neg.mpr hpc) hrpneg
    have hj := hJpos s (hAdm_s c) hscont hsnonneg ⟨p, hpS, hsp⟩
    rw [hcombine c, h₀, h₁] at hj
    linarith
  · have hL := nonneg_on_of_pos_at_of_no_zero hsegL hrL ⟨hpS, hpc⟩ hrppos hzeroL
    have hR := nonpos_on_of_neg_at_of_no_zero hsegR hrR ⟨hqS, hcq⟩ hrqneg hzeroR
    let s := fun x ↦ (x - c) * r x
    have hscont : ContinuousOn s S := (continuousOn_id.sub continuousOn_const).mul hr
    have hsnonpos : ∀ x ∈ S, s x ≤ 0 := by
      intro x hx
      rcases lt_trichotomy x c with hxc | hxc | hxc
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxc.le) (hL x ⟨hx, hxc⟩)
      · subst x; simp [s]
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hxc.le) (hR x ⟨hx, hxc⟩)
    have hsp : s p < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hpc) hrppos
    have hj := hneg_of_nonpos s (hAdm_s c) hscont hsnonpos ⟨p, hpS, hsp⟩
    rw [hcombine c, h₀, h₁] at hj
    linarith
  · have hL := nonneg_on_of_pos_at_of_no_zero hsegL hrL ⟨hpS, hpc⟩ hrppos hzeroL
    have hR := nonneg_on_of_pos_at_of_no_zero hsegR hrR ⟨hqS, hcq⟩ hrqpos hzeroR
    have hall : ∀ x ∈ S, 0 ≤ r x := by
      intro x hx
      rcases lt_trichotomy x c with hxc | hxc | hxc
      · exact hL x ⟨hx, hxc⟩
      · subst x; simp [hrc]
      · exact hR x ⟨hx, hxc⟩
    have := hJpos r hAdm_r hr hall ⟨p, hpS, hrppos⟩
    linarith

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/SetIntegralMomentZeros.lean` -/



open Real Set MeasureTheory Filter Metric
open scoped Topology

namespace LogConcaveClaimI

def weightedSetFunctional (S : Set ℝ) (w q : ℝ → ℝ) : ℝ :=
  ∫ x in S, q x * w x

def WeightedIntegrableOn (S : Set ℝ) (w q : ℝ → ℝ) : Prop :=
  IntegrableOn (fun x ↦ q x * w x) S volume

lemma weightedSetFunctional_neg (S : Set ℝ) (w q : ℝ → ℝ) :
    weightedSetFunctional S w (fun x ↦ -q x) = -weightedSetFunctional S w q := by
  rw [weightedSetFunctional, weightedSetFunctional, ← MeasureTheory.integral_neg]
  congr 1
  funext x
  ring

lemma weightedIntegrableOn_neg {S : Set ℝ} {w q : ℝ → ℝ}
    (h : WeightedIntegrableOn S w q) :
    WeightedIntegrableOn S w (fun x ↦ -q x) := by
  apply h.neg.congr_fun_ae
  filter_upwards with x
  change -(q x * w x) = -q x * w x
  ring

lemma strictlyPositiveFunctional_weightedSetIntegral
    {S : Set ℝ} (hSopen : IsOpen S) {w : ℝ → ℝ}
    (hwpos : ∀ x ∈ S, 0 < w x) :
    StrictlyPositiveFunctionalOn S (weightedSetFunctional S w)
      (WeightedIntegrableOn S w) := by
  intro q hqint hq hqnonneg hqstrict
  obtain ⟨p, hpS, hqp⟩ := hqstrict
  have hq_at : ContinuousAt q p := hq.continuousAt (hSopen.mem_nhds hpS)
  have hq_event : ∀ᶠ x in 𝓝 p, 0 < q x :=
    hq_at (isOpen_Ioi.mem_nhds hqp)
  obtain ⟨ε₁, hε₁, hballq⟩ := Metric.eventually_nhds_iff_ball.mp hq_event
  obtain ⟨ε₂, hε₂, hballS⟩ := Metric.mem_nhds_iff.mp (hSopen.mem_nhds hpS)
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hball : ball p ε ⊆ Function.support (fun x ↦ q x * w x) ∩ S := by
    intro x hx
    have hxq : 0 < q x := hballq x
      (mem_ball'.2 ((mem_ball'.1 hx).trans_le (min_le_left _ _)))
    have hxS : x ∈ S := hballS
      (mem_ball'.2 ((mem_ball'.1 hx).trans_le (min_le_right _ _)))
    exact ⟨mul_ne_zero hxq.ne' (hwpos x hxS).ne', hxS⟩
  have hsupport : 0 < volume (Function.support (fun x ↦ q x * w x) ∩ S) :=
    (Metric.isOpen_ball.measure_pos volume ⟨p, mem_ball_self hε⟩).trans_le
      (measure_mono hball)
  apply (setIntegral_pos_iff_support_of_nonneg_ae ?_ hqint).2 hsupport
  filter_upwards [ae_restrict_mem hSopen.measurableSet] with x hx
  exact mul_nonneg (hqnonneg x hx) (hwpos x hx).le

/-! Weighted set-integral form of the two-zero lemma, valid without boundedness of `S`. -/
theorem two_zeros_of_weighted_set_moments
    {S : Set ℝ} (hS : OpenOrderInterval S) (hSopen : IsOpen S)
    {r w : ℝ → ℝ} (hr : ContinuousOn r S)
    (hwpos : ∀ x ∈ S, 0 < w x)
    (hrint : IntegrableOn (fun x ↦ r x * w x) S volume)
    (hxrint : IntegrableOn (fun x ↦ x * r x * w x) S volume)
    (h₀ : (∫ x in S, r x * w x) = 0)
    (h₁ : (∫ x in S, x * r x * w x) = 0) :
    ∃ x₁ x₂, x₁ ∈ S ∧ x₂ ∈ S ∧ x₁ < x₂ ∧ r x₁ = 0 ∧ r x₂ = 0 := by
  let J := weightedSetFunctional S w
  have hAdm_r : WeightedIntegrableOn S w r := hrint
  have hAdm_s : ∀ c, WeightedIntegrableOn S w (fun x ↦ (x - c) * r x) := by
    intro c
    have h := hxrint.sub (hrint.const_mul c)
    apply h.congr_fun_ae
    filter_upwards with x
    change x * r x * w x - c * (r x * w x) = (x - c) * r x * w x
    ring
  apply two_zeros_of_positive_functional hS
    (strictlyPositiveFunctional_weightedSetIntegral hSopen hwpos)
    (weightedSetFunctional_neg S w) weightedIntegrableOn_neg hr hAdm_r hAdm_s
  · simpa [J, weightedSetFunctional] using h₀
  · simpa [J, weightedSetFunctional, mul_assoc] using h₁
  · intro c
    have hi₀ : IntegrableOn (fun x ↦ r x * w x) S volume := hrint
    have hi₁ : IntegrableOn (fun x ↦ x * r x * w x) S volume := hxrint
    simp only [weightedSetFunctional]
    change (∫ x in S, (x - c) * r x * w x) =
      (∫ x in S, x * r x * w x) - c * (∫ x in S, r x * w x)
    calc
      (∫ x in S, (x - c) * r x * w x) =
          ∫ x in S, (x * r x * w x) - c * (r x * w x) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            ring
      _ = (∫ x in S, x * r x * w x) - ∫ x in S, c * (r x * w x) :=
        integral_sub hi₁ (hi₀.const_mul c)
      _ = _ := by rw [MeasureTheory.integral_const_mul]

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/MomentNondegenerate.lean` -/



open Real Set MeasureTheory

namespace LogConcaveClaimI

def weightedMoment (S : Set ℝ) (w : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in S, x ^ n * w x

def quadratic (a b c x : ℝ) : ℝ := a + b * x + c * x ^ 2

lemma continuous_quadratic (a b c : ℝ) : Continuous (quadratic a b c) := by
  unfold quadratic
  fun_prop

private lemma integrable_quadratic_mul
    {S : Set ℝ} {w : ℝ → ℝ} {a b c : ℝ}
    (h0 : IntegrableOn (fun x ↦ x ^ 0 * w x) S volume)
    (h1 : IntegrableOn (fun x ↦ x ^ 1 * w x) S volume)
    (h2 : IntegrableOn (fun x ↦ x ^ 2 * w x) S volume) :
    IntegrableOn (fun x ↦ quadratic a b c x * w x) S volume := by
  have h : IntegrableOn
      (((fun x ↦ a * (x ^ 0 * w x)) + fun x ↦ b * (x ^ 1 * w x)) +
        fun x ↦ c * (x ^ 2 * w x)) S volume :=
    ((h0.const_mul a).add (h1.const_mul b)).add (h2.const_mul c)
  apply h.congr_fun_ae
  filter_upwards with x
  simp [quadratic]
  ring

private lemma integrable_x_quadratic_mul
    {S : Set ℝ} {w : ℝ → ℝ} {a b c : ℝ}
    (h1 : IntegrableOn (fun x ↦ x ^ 1 * w x) S volume)
    (h2 : IntegrableOn (fun x ↦ x ^ 2 * w x) S volume)
    (h3 : IntegrableOn (fun x ↦ x ^ 3 * w x) S volume) :
    IntegrableOn (fun x ↦ x * quadratic a b c x * w x) S volume := by
  have h : IntegrableOn
      (((fun x ↦ a * (x ^ 1 * w x)) + fun x ↦ b * (x ^ 2 * w x)) +
        fun x ↦ c * (x ^ 3 * w x)) S volume :=
    ((h1.const_mul a).add (h2.const_mul b)).add (h3.const_mul c)
  apply h.congr_fun_ae
  filter_upwards with x
  simp [quadratic]
  ring

private lemma integral_quadratic_mul_eq
    {S : Set ℝ} {w : ℝ → ℝ} {a b c : ℝ}
    (h0 : IntegrableOn (fun x ↦ x ^ 0 * w x) S volume)
    (h1 : IntegrableOn (fun x ↦ x ^ 1 * w x) S volume)
    (h2 : IntegrableOn (fun x ↦ x ^ 2 * w x) S volume) :
    (∫ x in S, quadratic a b c x * w x) =
      a * weightedMoment S w 0 + b * weightedMoment S w 1 + c * weightedMoment S w 2 := by
  change (∫ x in S, quadratic a b c x * w x) =
    a * (∫ x in S, x ^ 0 * w x) + b * (∫ x in S, x ^ 1 * w x) +
      c * (∫ x in S, x ^ 2 * w x)
  calc
    _ = ∫ x in S, a * (x ^ 0 * w x) + b * (x ^ 1 * w x) +
        c * (x ^ 2 * w x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          simp [quadratic]
          ring
    _ = _ := by
      change (∫ x in S, ((fun x ↦ a * (x ^ 0 * w x)) +
          fun x ↦ b * (x ^ 1 * w x)) x + c * (x ^ 2 * w x)) = _
      rw [integral_add ((h0.const_mul a).add (h1.const_mul b)) (h2.const_mul c)]
      change (∫ x in S, a * (x ^ 0 * w x) + b * (x ^ 1 * w x)) +
          (∫ x in S, c * (x ^ 2 * w x)) = _
      rw [integral_add (h0.const_mul a) (h1.const_mul b),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]

private lemma integral_x_quadratic_mul_eq
    {S : Set ℝ} {w : ℝ → ℝ} {a b c : ℝ}
    (h1 : IntegrableOn (fun x ↦ x ^ 1 * w x) S volume)
    (h2 : IntegrableOn (fun x ↦ x ^ 2 * w x) S volume)
    (h3 : IntegrableOn (fun x ↦ x ^ 3 * w x) S volume) :
    (∫ x in S, x * quadratic a b c x * w x) =
      a * weightedMoment S w 1 + b * weightedMoment S w 2 + c * weightedMoment S w 3 := by
  change (∫ x in S, x * quadratic a b c x * w x) =
    a * (∫ x in S, x ^ 1 * w x) + b * (∫ x in S, x ^ 2 * w x) +
      c * (∫ x in S, x ^ 3 * w x)
  calc
    _ = ∫ x in S, a * (x ^ 1 * w x) + b * (x ^ 2 * w x) +
        c * (x ^ 3 * w x) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          simp [quadratic]
          ring
    _ = _ := by
      change (∫ x in S, ((fun x ↦ a * (x ^ 1 * w x)) +
          fun x ↦ b * (x ^ 2 * w x)) x + c * (x ^ 3 * w x)) = _
      rw [integral_add ((h1.const_mul a).add (h2.const_mul b)) (h3.const_mul c)]
      change (∫ x in S, a * (x ^ 1 * w x) + b * (x ^ 2 * w x)) +
          (∫ x in S, c * (x ^ 3 * w x)) = _
      rw [integral_add (h1.const_mul a) (h2.const_mul b),
        MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]

/-! Positivity on two separated intervals makes the four moment columns in the KKT
Jacobian nondegenerate. -/
theorem separated_moments_quadratic_nondegenerate
    {SL SR : Set ℝ} (hSL : OpenOrderInterval SL) (hSR : OpenOrderInterval SR)
    (hSLopen : IsOpen SL) (hSRopen : IsOpen SR)
    (hsep : ∀ ⦃x⦄, x ∈ SL → ∀ ⦃y⦄, y ∈ SR → x < y)
    {w : ℝ → ℝ} (hwL : ContinuousOn w SL) (hwR : ContinuousOn w SR)
    (hwposL : ∀ x ∈ SL, 0 < w x) (hwposR : ∀ x ∈ SR, 0 < w x)
    (hintL : ∀ n ≤ 3, IntegrableOn (fun x ↦ x ^ n * w x) SL volume)
    (hintR : ∀ n ≤ 3, IntegrableOn (fun x ↦ x ^ n * w x) SR volume) :
    ∀ a b c : ℝ,
      a * weightedMoment SL w 0 + b * weightedMoment SL w 1 + c * weightedMoment SL w 2 = 0 →
      a * weightedMoment SL w 1 + b * weightedMoment SL w 2 + c * weightedMoment SL w 3 = 0 →
      a * weightedMoment SR w 0 + b * weightedMoment SR w 1 + c * weightedMoment SR w 2 = 0 →
      a * weightedMoment SR w 1 + b * weightedMoment SR w 2 + c * weightedMoment SR w 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
  intro a b c hL0 hL1 hR0 hR1
  have hiL0 := hintL 0 (by norm_num)
  have hiL1 := hintL 1 (by norm_num)
  have hiL2 := hintL 2 (by norm_num)
  have hiL3 := hintL 3 (by norm_num)
  have hiR0 := hintR 0 (by norm_num)
  have hiR1 := hintR 1 (by norm_num)
  have hiR2 := hintR 2 (by norm_num)
  have hiR3 := hintR 3 (by norm_num)
  obtain ⟨x₁, x₂, hx₁, hx₂, hx₁x₂, hqx₁, hqx₂⟩ :=
    two_zeros_of_weighted_set_moments hSL hSLopen
      (continuous_quadratic a b c).continuousOn hwposL
      (integrable_quadratic_mul hiL0 hiL1 hiL2)
      (integrable_x_quadratic_mul hiL1 hiL2 hiL3)
      ((integral_quadratic_mul_eq hiL0 hiL1 hiL2).trans hL0)
      ((integral_x_quadratic_mul_eq hiL1 hiL2 hiL3).trans hL1)
  obtain ⟨y₁, y₂, hy₁, hy₂, hy₁y₂, hqy₁, hqy₂⟩ :=
    two_zeros_of_weighted_set_moments hSR hSRopen
      (continuous_quadratic a b c).continuousOn hwposR
      (integrable_quadratic_mul hiR0 hiR1 hiR2)
      (integrable_x_quadratic_mul hiR1 hiR2 hiR3)
      ((integral_quadratic_mul_eq hiR0 hiR1 hiR2).trans hR0)
      ((integral_x_quadratic_mul_eq hiR1 hiR2 hiR3).trans hR1)
  have hx₂y₁ : x₂ < y₁ := hsep hx₂ hy₁
  have he12 : (x₁ - x₂) * (b + c * (x₁ + x₂)) = 0 := by
    calc
      _ = quadratic a b c x₁ - quadratic a b c x₂ := by simp [quadratic]; ring
      _ = 0 := by rw [hqx₁, hqx₂]; ring
  have he2y : (x₂ - y₁) * (b + c * (x₂ + y₁)) = 0 := by
    calc
      _ = quadratic a b c x₂ - quadratic a b c y₁ := by simp [quadratic]; ring
      _ = 0 := by rw [hqx₂, hqy₁]; ring
  have hlin12 : b + c * (x₁ + x₂) = 0 :=
    (mul_eq_zero.mp he12).resolve_left (sub_ne_zero.mpr (ne_of_lt hx₁x₂))
  have hlin2y : b + c * (x₂ + y₁) = 0 :=
    (mul_eq_zero.mp he2y).resolve_left (sub_ne_zero.mpr (ne_of_lt hx₂y₁))
  have hc0 : c = 0 := by
    have hprod : c * (x₁ - y₁) = 0 := by nlinarith
    exact (mul_eq_zero.mp hprod).resolve_right
      (sub_ne_zero.mpr (ne_of_lt (hx₁x₂.trans hx₂y₁)))
  have hb0 : b = 0 := by
    rw [hc0, zero_mul, add_zero] at hlin12
    exact hlin12
  have ha0 : a = 0 := by
    simpa [quadratic, hb0, hc0] using hqx₁
  exact ⟨ha0, hb0, hc0⟩

/-! The same rank lemma with independent positive weights on the two sides.
No comparison between the weights is used: the proof only extracts two zeros
of the same quadratic from each side. -/
theorem separated_moments_quadratic_nondegenerate_two_weights
    {SL SR : Set ℝ} (hSL : OpenOrderInterval SL) (hSR : OpenOrderInterval SR)
    (hSLopen : IsOpen SL) (hSRopen : IsOpen SR)
    (hsep : ∀ ⦃x⦄, x ∈ SL → ∀ ⦃y⦄, y ∈ SR → x < y)
    {wL wR : ℝ → ℝ}
    (hwposL : ∀ x ∈ SL, 0 < wL x) (hwposR : ∀ x ∈ SR, 0 < wR x)
    (hintL : ∀ n ≤ 3, IntegrableOn (fun x ↦ x ^ n * wL x) SL volume)
    (hintR : ∀ n ≤ 3, IntegrableOn (fun x ↦ x ^ n * wR x) SR volume) :
    ∀ a b c : ℝ,
      a * weightedMoment SL wL 0 + b * weightedMoment SL wL 1 +
          c * weightedMoment SL wL 2 = 0 →
      a * weightedMoment SL wL 1 + b * weightedMoment SL wL 2 +
          c * weightedMoment SL wL 3 = 0 →
      a * weightedMoment SR wR 0 + b * weightedMoment SR wR 1 +
          c * weightedMoment SR wR 2 = 0 →
      a * weightedMoment SR wR 1 + b * weightedMoment SR wR 2 +
          c * weightedMoment SR wR 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
  intro a b c hL0 hL1 hR0 hR1
  have hiL0 := hintL 0 (by norm_num)
  have hiL1 := hintL 1 (by norm_num)
  have hiL2 := hintL 2 (by norm_num)
  have hiL3 := hintL 3 (by norm_num)
  have hiR0 := hintR 0 (by norm_num)
  have hiR1 := hintR 1 (by norm_num)
  have hiR2 := hintR 2 (by norm_num)
  have hiR3 := hintR 3 (by norm_num)
  obtain ⟨x₁, x₂, hx₁, hx₂, hx₁x₂, hqx₁, hqx₂⟩ :=
    two_zeros_of_weighted_set_moments hSL hSLopen
      (continuous_quadratic a b c).continuousOn hwposL
      (integrable_quadratic_mul hiL0 hiL1 hiL2)
      (integrable_x_quadratic_mul hiL1 hiL2 hiL3)
      ((integral_quadratic_mul_eq hiL0 hiL1 hiL2).trans hL0)
      ((integral_x_quadratic_mul_eq hiL1 hiL2 hiL3).trans hL1)
  obtain ⟨y₁, y₂, hy₁, hy₂, hy₁y₂, hqy₁, hqy₂⟩ :=
    two_zeros_of_weighted_set_moments hSR hSRopen
      (continuous_quadratic a b c).continuousOn hwposR
      (integrable_quadratic_mul hiR0 hiR1 hiR2)
      (integrable_x_quadratic_mul hiR1 hiR2 hiR3)
      ((integral_quadratic_mul_eq hiR0 hiR1 hiR2).trans hR0)
      ((integral_x_quadratic_mul_eq hiR1 hiR2 hiR3).trans hR1)
  have hx₂y₁ : x₂ < y₁ := hsep hx₂ hy₁
  have he12 : (x₁ - x₂) * (b + c * (x₁ + x₂)) = 0 := by
    calc
      _ = quadratic a b c x₁ - quadratic a b c x₂ := by simp [quadratic]; ring
      _ = 0 := by rw [hqx₁, hqx₂]; ring
  have he2y : (x₂ - y₁) * (b + c * (x₂ + y₁)) = 0 := by
    calc
      _ = quadratic a b c x₂ - quadratic a b c y₁ := by simp [quadratic]; ring
      _ = 0 := by rw [hqx₂, hqy₁]; ring
  have hlin12 : b + c * (x₁ + x₂) = 0 :=
    (mul_eq_zero.mp he12).resolve_left (sub_ne_zero.mpr (ne_of_lt hx₁x₂))
  have hlin2y : b + c * (x₂ + y₁) = 0 :=
    (mul_eq_zero.mp he2y).resolve_left (sub_ne_zero.mpr (ne_of_lt hx₂y₁))
  have hc0 : c = 0 := by
    have hprod : c * (x₁ - y₁) = 0 := by nlinarith
    exact (mul_eq_zero.mp hprod).resolve_right
      (sub_ne_zero.mpr (ne_of_lt (hx₁x₂.trans hx₂y₁)))
  have hb0 : b = 0 := by
    rw [hc0, zero_mul, add_zero] at hlin12
    exact hlin12
  have ha0 : a = 0 := by
    simpa [quadratic, hb0, hc0] using hqx₁
  exact ⟨ha0, hb0, hc0⟩

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/CompactClaimI.lean` -/



open Real Set Filter Topology MeasureTheory intervalIntegral
open scoped Topology Interval

namespace LogConcaveClaimI

def compactKinkDomain : Set CompactParam :=
  {p | p 0 < p 5 ∧ p 5 < p 1 ∧ 0 < p 4}

lemma isOpen_compactKinkDomain : IsOpen compactKinkDomain := by
  change IsOpen ({p : CompactParam | p 0 < p 5} ∩
    ({p : CompactParam | p 5 < p 1} ∩ {p : CompactParam | (0 : ℝ) < p 4}))
  exact (isOpen_lt (compactCoord 0).continuous (compactCoord 5).continuous).inter
    ((isOpen_lt (compactCoord 5).continuous (compactCoord 1).continuous).inter
      (isOpen_lt continuous_const (compactCoord 4).continuous))

lemma localExtrOn_fiber_of_domain
    {Phi : CompactParam → ℝ} {M : CompactParam → (Fin 3 → ℝ)} {p : CompactParam}
    (hp : p ∈ compactKinkDomain)
    (h : IsLocalExtrOn Phi ({u | M u = M p} ∩ compactKinkDomain) p) :
    IsLocalExtrOn Phi {u | M u = M p} p := by
  change IsExtrFilter Phi (𝓝[({u | M u = M p} ∩ compactKinkDomain)] p) p at h
  change IsExtrFilter Phi (𝓝[{u | M u = M p}] p) p
  rw [nhdsWithin_inter_of_mem'
    (mem_nhdsWithin_of_mem_nhds (isOpen_compactKinkDomain.mem_nhds hp))] at h
  exact h

def compactLeftWeight (p : CompactParam) (x : ℝ) : ℝ :=
  exp (leftExponent p x)

def compactRightWeight (p : CompactParam) (x : ℝ) : ℝ :=
  exp (rightExponent p x)

lemma continuous_compactLeftWeight (p : CompactParam) :
    Continuous (compactLeftWeight p) := by
  unfold compactLeftWeight leftExponent
  fun_prop

lemma continuous_compactRightWeight (p : CompactParam) :
    Continuous (compactRightWeight p) := by
  unfold compactRightWeight rightExponent
  fun_prop

lemma compactLeftMoment_eq_weightedMoment {p : CompactParam}
    (hAm : p 0 ≤ p 5) (n : ℕ) :
    compactLeftMoment p n =
      weightedMoment (Ioo (p 0) (p 5)) (compactLeftWeight p) n := by
  unfold compactLeftMoment leftIntegral leftIntegrand weightedMoment compactLeftWeight
  rw [intervalIntegral.integral_of_le hAm,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

lemma compactRightMoment_eq_weightedMoment {p : CompactParam}
    (hmB : p 5 ≤ p 1) (n : ℕ) :
    compactRightMoment p n =
      weightedMoment (Ioo (p 5) (p 1)) (compactRightWeight p) n := by
  unfold compactRightMoment rightIntegral rightIntegrand weightedMoment compactRightWeight
  rw [intervalIntegral.integral_of_le hmB,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem compact_moments_quadratic_nondegenerate {p : CompactParam}
    (hAm : p 0 < p 5) (hmB : p 5 < p 1) :
    ∀ a b c : ℝ,
      a * compactLeftMoment p 0 + b * compactLeftMoment p 1 +
          c * compactLeftMoment p 2 = 0 →
      a * compactLeftMoment p 1 + b * compactLeftMoment p 2 +
          c * compactLeftMoment p 3 = 0 →
      a * compactRightMoment p 0 + b * compactRightMoment p 1 +
          c * compactRightMoment p 2 = 0 →
      a * compactRightMoment p 1 + b * compactRightMoment p 2 +
          c * compactRightMoment p 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
  have hbase := separated_moments_quadratic_nondegenerate_two_weights
    (openOrderInterval_Ioo hAm) (openOrderInterval_Ioo hmB)
    isOpen_Ioo isOpen_Ioo
    (fun _ hx _ hy ↦ hx.2.trans hy.1)
    (fun x hx ↦ exp_pos _)
    (fun x hx ↦ exp_pos _)
    (fun n hn ↦ ((continuous_id.pow n).mul
      (continuous_compactLeftWeight p)).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    (fun n hn ↦ ((continuous_id.pow n).mul
      (continuous_compactRightWeight p)).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
  intro a b c hL0 hL1 hR0 hR1
  apply hbase a b c
  · change a * weightedMoment (Ioo (p 0) (p 5)) (compactLeftWeight p) 0 +
        b * weightedMoment (Ioo (p 0) (p 5)) (compactLeftWeight p) 1 +
        c * weightedMoment (Ioo (p 0) (p 5)) (compactLeftWeight p) 2 = 0
    rw [← compactLeftMoment_eq_weightedMoment hAm.le 0,
      ← compactLeftMoment_eq_weightedMoment hAm.le 1,
      ← compactLeftMoment_eq_weightedMoment hAm.le 2]
    exact hL0
  · change a * weightedMoment (Ioo (p 0) (p 5)) (compactLeftWeight p) 1 +
        b * weightedMoment (Ioo (p 0) (p 5)) (compactLeftWeight p) 2 +
        c * weightedMoment (Ioo (p 0) (p 5)) (compactLeftWeight p) 3 = 0
    rw [← compactLeftMoment_eq_weightedMoment hAm.le 1,
      ← compactLeftMoment_eq_weightedMoment hAm.le 2,
      ← compactLeftMoment_eq_weightedMoment hAm.le 3]
    exact hL1
  · change a * weightedMoment (Ioo (p 5) (p 1)) (compactRightWeight p) 0 +
        b * weightedMoment (Ioo (p 5) (p 1)) (compactRightWeight p) 1 +
        c * weightedMoment (Ioo (p 5) (p 1)) (compactRightWeight p) 2 = 0
    rw [← compactRightMoment_eq_weightedMoment hmB.le 0,
      ← compactRightMoment_eq_weightedMoment hmB.le 1,
      ← compactRightMoment_eq_weightedMoment hmB.le 2]
    exact hR0
  · change a * weightedMoment (Ioo (p 5) (p 1)) (compactRightWeight p) 1 +
        b * weightedMoment (Ioo (p 5) (p 1)) (compactRightWeight p) 2 +
        c * weightedMoment (Ioo (p 5) (p 1)) (compactRightWeight p) 3 = 0
    rw [← compactRightMoment_eq_weightedMoment hmB.le 1,
      ← compactRightMoment_eq_weightedMoment hmB.le 2,
      ← compactRightMoment_eq_weightedMoment hmB.le 3]
    exact hR1

lemma intervalIntegral_residual_times_weight
    (alpha lambda₀ lambda₁ lambda₂ a b : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    (∫ x in a..b, residual alpha lambda₀ lambda₁ lambda₂ x * w x) =
      (∫ x in a..b, gAlpha alpha x * w x) -
        lambda₀ * (∫ x in a..b, x ^ 0 * w x) -
        lambda₁ * (∫ x in a..b, x ^ 1 * w x) -
        lambda₂ * (∫ x in a..b, x ^ 2 * w x) := by
  have hg : IntervalIntegrable (fun x ↦ gAlpha alpha x * w x) volume a b :=
    ((continuous_gAlpha alpha).mul hw).intervalIntegrable _ _
  have h0 : IntervalIntegrable (fun x ↦ x ^ 0 * w x) volume a b :=
    ((continuous_id.pow 0).mul hw).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun x ↦ x ^ 1 * w x) volume a b :=
    ((continuous_id.pow 1).mul hw).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x ↦ x ^ 2 * w x) volume a b :=
    ((continuous_id.pow 2).mul hw).intervalIntegrable _ _
  calc
    (∫ x in a..b, residual alpha lambda₀ lambda₁ lambda₂ x * w x) =
        ∫ x in a..b,
          ((gAlpha alpha x * w x - lambda₀ * (x ^ 0 * w x)) -
            lambda₁ * (x ^ 1 * w x)) - lambda₂ * (x ^ 2 * w x) := by
              apply intervalIntegral.integral_congr
              intro x hx
              simp only [residual]
              ring
    _ = _ := by
      rw [intervalIntegral.integral_sub
          ((hg.sub (h0.const_mul lambda₀)).sub (h1.const_mul lambda₁))
          (h2.const_mul lambda₂),
        intervalIntegral.integral_sub (hg.sub (h0.const_mul lambda₀))
          (h1.const_mul lambda₁),
        intervalIntegral.integral_sub hg (h0.const_mul lambda₀)]
      simp only [intervalIntegral.integral_const_mul]

lemma intervalIntegral_x_residual_times_weight
    (alpha lambda₀ lambda₁ lambda₂ a b : ℝ) {w : ℝ → ℝ} (hw : Continuous w) :
    (∫ x in a..b, x * residual alpha lambda₀ lambda₁ lambda₂ x * w x) =
      (∫ x in a..b, x * gAlpha alpha x * w x) -
        lambda₀ * (∫ x in a..b, x ^ 1 * w x) -
        lambda₁ * (∫ x in a..b, x ^ 2 * w x) -
        lambda₂ * (∫ x in a..b, x ^ 3 * w x) := by
  have hg : IntervalIntegrable
      (fun x ↦ x * gAlpha alpha x * w x) volume a b :=
    ((continuous_id.mul (continuous_gAlpha alpha)).mul hw).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun x ↦ x ^ 1 * w x) volume a b :=
    ((continuous_id.pow 1).mul hw).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x ↦ x ^ 2 * w x) volume a b :=
    ((continuous_id.pow 2).mul hw).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun x ↦ x ^ 3 * w x) volume a b :=
    ((continuous_id.pow 3).mul hw).intervalIntegrable _ _
  calc
    (∫ x in a..b, x * residual alpha lambda₀ lambda₁ lambda₂ x * w x) =
        ∫ x in a..b,
          ((x * gAlpha alpha x * w x - lambda₀ * (x ^ 1 * w x)) -
            lambda₁ * (x ^ 2 * w x)) - lambda₂ * (x ^ 3 * w x) := by
              apply intervalIntegral.integral_congr
              intro x hx
              simp only [residual]
              ring
    _ = _ := by
      rw [intervalIntegral.integral_sub
          ((hg.sub (h1.const_mul lambda₀)).sub (h2.const_mul lambda₁))
          (h3.const_mul lambda₂),
        intervalIntegral.integral_sub (hg.sub (h1.const_mul lambda₀))
          (h2.const_mul lambda₁),
        intervalIntegral.integral_sub hg (h1.const_mul lambda₀)]
      simp only [intervalIntegral.integral_const_mul]

/-! A genuine compact two-piece exponential cannot be a constrained local
extremum of the `gAlpha` objective on a fixed first-three-moment fibre. -/
theorem no_compact_genuine_kink_local_extremum
    {alpha : ℝ} (halpha : 0 < alpha) {p : CompactParam}
    (hp : p ∈ compactKinkDomain)
    (hlocal : IsLocalExtrOn (compactIntegral (gAlpha alpha))
      ({u | compactMomentMap u = compactMomentMap p} ∩ compactKinkDomain) p) :
    False := by
  have hp' := hp
  change p 0 < p 5 ∧ p 5 < p 1 ∧ 0 < p 4 at hp
  rcases hp with ⟨hAm, hmB, hdelta⟩
  have hmax : IsLocalExtrOn (compactIntegral (gAlpha alpha))
      {u | compactMomentMap u = compactMomentMap p} p :=
    localExtrOn_fiber_of_domain hp' hlocal
  have hpoly := compact_moments_quadratic_nondegenerate hAm hmB
  have hdelta0 : p 4 ≠ 0 := ne_of_gt hdelta
  have hrhoA : -exp (leftExponent p (p 0)) ≠ 0 :=
    neg_ne_zero.mpr (exp_ne_zero _)
  have hrhoB : exp (rightExponent p (p 1)) ≠ 0 := exp_ne_zero _
  obtain ⟨lambda₀, lambda₁, lambda₂,
      hL0, hL1, hR0, hR1, hA, hB⟩ :=
    compact_KKT_residual_equations
      (M := compactMomentMap) (Phi := compactIntegral (gAlpha alpha))
      (theta := p)
      (L := compactLeftMoment p) (R := compactRightMoment p)
      (A := p 0) (B := p 1) (m := p 5) (delta := p 4)
      (rhoA := -exp (leftExponent p (p 0)))
      (rhoB := exp (rightExponent p (p 1)))
      (HL0 := leftIntegral (gAlpha alpha) p)
      (HL1 := leftIntegral (fun x ↦ x * gAlpha alpha x) p)
      (HR0 := rightIntegral (gAlpha alpha) p)
      (HR1 := rightIntegral (fun x ↦ x * gAlpha alpha x) p)
      (hA := gAlpha alpha (p 0)) (hB := gAlpha alpha (p 1))
      hdelta0 hrhoA hrhoB hpoly hmax
      (hasStrictFDerivAt_compactMomentMap p)
      (hasStrictFDerivAt_compactIntegral (continuous_gAlpha alpha) p)
  have hzL0 :
      (∫ x in p 0..p 5,
        residual alpha lambda₀ lambda₁ lambda₂ x * compactLeftWeight p x) = 0 := by
    rw [intervalIntegral_residual_times_weight alpha lambda₀ lambda₁ lambda₂
      (p 0) (p 5) (continuous_compactLeftWeight p)]
    change leftIntegral (gAlpha alpha) p -
      lambda₀ * compactLeftMoment p 0 -
      lambda₁ * compactLeftMoment p 1 -
      lambda₂ * compactLeftMoment p 2 = 0
    linarith
  have hzL1 :
      (∫ x in p 0..p 5,
        x * residual alpha lambda₀ lambda₁ lambda₂ x * compactLeftWeight p x) = 0 := by
    rw [intervalIntegral_x_residual_times_weight alpha lambda₀ lambda₁ lambda₂
      (p 0) (p 5) (continuous_compactLeftWeight p)]
    change leftIntegral (fun x ↦ x * gAlpha alpha x) p -
      lambda₀ * compactLeftMoment p 1 -
      lambda₁ * compactLeftMoment p 2 -
      lambda₂ * compactLeftMoment p 3 = 0
    linarith
  have hzR0 :
      (∫ x in p 5..p 1,
        residual alpha lambda₀ lambda₁ lambda₂ x * compactRightWeight p x) = 0 := by
    rw [intervalIntegral_residual_times_weight alpha lambda₀ lambda₁ lambda₂
      (p 5) (p 1) (continuous_compactRightWeight p)]
    change rightIntegral (gAlpha alpha) p -
      lambda₀ * compactRightMoment p 0 -
      lambda₁ * compactRightMoment p 1 -
      lambda₂ * compactRightMoment p 2 = 0
    linarith
  have hzR1 :
      (∫ x in p 5..p 1,
        x * residual alpha lambda₀ lambda₁ lambda₂ x * compactRightWeight p x) = 0 := by
    rw [intervalIntegral_x_residual_times_weight alpha lambda₀ lambda₁ lambda₂
      (p 5) (p 1) (continuous_compactRightWeight p)]
    change rightIntegral (fun x ↦ x * gAlpha alpha x) p -
      lambda₀ * compactRightMoment p 1 -
      lambda₁ * compactRightMoment p 2 -
      lambda₂ * compactRightMoment p 3 = 0
    linarith
  have hend : residual alpha lambda₀ lambda₁ lambda₂ (p 0) = 0 := by
    unfold residual
    linarith
  exact compact_genuine_kink_contradiction_two_weights halpha hAm hmB
    (continuous_compactLeftWeight p).continuousOn
    (continuous_compactRightWeight p).continuousOn
    (fun x hx ↦ exp_pos _) (fun x hx ↦ exp_pos _)
    hzL0 hzL1 hzR0 hzR1 (Or.inl hend)

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/HalfLineKKTAssembly.lean` -/



namespace LogConcaveClaimI

def finiteLeftMomentJacobian
    (L R : ℕ → ℝ) (A m delta rhoA : ℝ) :
    (Fin 5 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v k := momentVariationLeft L R A m delta rhoA v k
  map_add' v w := by ext k; simp [momentVariationLeft]; ring
  map_smul' c v := by ext k; simp [momentVariationLeft]; ring

def finiteLeftMomentJacobianCLM
    (L R : ℕ → ℝ) (A m delta rhoA : ℝ) :
    (Fin 5 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  (finiteLeftMomentJacobian L R A m delta rhoA).toContinuousLinearMap

def finiteLeftObjectiveJacobian
    (HL0 HL1 HR0 HR1 hA m delta rhoA : ℝ) :
    (Fin 5 → ℝ) →ₗ[ℝ] ℝ where
  toFun v := objectiveVariationLeft HL0 HL1 HR0 HR1 hA m delta rhoA v
  map_add' v w := by simp [objectiveVariationLeft]; ring
  map_smul' c v := by simp [objectiveVariationLeft]; ring

def finiteLeftObjectiveJacobianCLM
    (HL0 HL1 HR0 HR1 hA m delta rhoA : ℝ) :
    (Fin 5 → ℝ) →L[ℝ] ℝ :=
  (finiteLeftObjectiveJacobian HL0 HL1 HR0 HR1 hA m delta rhoA).toContinuousLinearMap

lemma finiteLeftMomentJacobian_surjective
    {L R : ℕ → ℝ} {A m delta rhoA : ℝ}
    (hdelta : delta ≠ 0)
    (hpoly : ∀ a b c : ℝ,
      a * L 0 + b * L 1 + c * L 2 = 0 →
      a * L 1 + b * L 2 + c * L 3 = 0 →
      a * R 0 + b * R 1 + c * R 2 = 0 →
      a * R 1 + b * R 2 + c * R 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0) :
    Function.Surjective (finiteLeftMomentJacobianCLM L R A m delta rhoA) := by
  intro y
  obtain ⟨u, hu⟩ := momentJacobian_surjective (m := m) hdelta hpoly y
  let v : Fin 5 → ℝ := fun i ↦
    if i = 1 then u 0 else if i = 2 then u 1 else
    if i = 3 then u 2 else if i = 4 then u 3 else 0
  refine ⟨v, ?_⟩
  ext k
  have hk := congrFun hu k
  fin_cases k <;>
    norm_num [v, finiteLeftMomentJacobianCLM, finiteLeftMomentJacobian,
      momentVariationLeft, momentJacobian] at hk ⊢ <;>
    simp at hk ⊢ <;>
    exact hk

theorem finiteLeft_KKT_residual_equations
    {M : (Fin 5 → ℝ) → (Fin 3 → ℝ)}
    {Phi : (Fin 5 → ℝ) → ℝ} {theta : Fin 5 → ℝ}
    {L R : ℕ → ℝ} {A m delta rhoA : ℝ}
    {HL0 HL1 HR0 HR1 hA : ℝ}
    (hdelta : delta ≠ 0) (hrhoA : rhoA ≠ 0)
    (hpoly : ∀ a b c : ℝ,
      a * L 0 + b * L 1 + c * L 2 = 0 →
      a * L 1 + b * L 2 + c * L 3 = 0 →
      a * R 0 + b * R 1 + c * R 2 = 0 →
      a * R 1 + b * R 2 + c * R 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0)
    (hmax : IsLocalExtrOn Phi {x | M x = M theta} theta)
    (hM : HasStrictFDerivAt M
      (finiteLeftMomentJacobianCLM L R A m delta rhoA) theta)
    (hPhi : HasStrictFDerivAt Phi
      (finiteLeftObjectiveJacobianCLM
        HL0 HL1 HR0 HR1 hA m delta rhoA) theta) :
    ∃ lambda₀ lambda₁ lambda₂ : ℝ,
      HL0 = lambda₀ * L 0 + lambda₁ * L 1 + lambda₂ * L 2 ∧
      HL1 = lambda₀ * L 1 + lambda₁ * L 2 + lambda₂ * L 3 ∧
      HR0 = lambda₀ * R 0 + lambda₁ * R 1 + lambda₂ * R 2 ∧
      HR1 = lambda₀ * R 1 + lambda₁ * R 2 + lambda₂ * R 3 ∧
      hA = lambda₀ + lambda₁ * A + lambda₂ * A ^ 2 := by
  have hsurj := finiteLeftMomentJacobian_surjective
    (A := A) (m := m) (rhoA := rhoA) hdelta hpoly
  obtain ⟨Lambda, hLambda⟩ :=
    LogConcaveClaimI.IsLocalExtrOn.exists_normalized_lagrange_multiplier
      hmax hM hPhi hsurj
  let lambda₀ := Lambda (Pi.single (M := fun _ : Fin 3 ↦ ℝ) 0 1)
  let lambda₁ := Lambda (Pi.single (M := fun _ : Fin 3 ↦ ℝ) 1 1)
  let lambda₂ := Lambda (Pi.single (M := fun _ : Fin 3 ↦ ℝ) 2 1)
  have hfactor : ∀ v : Fin 5 → ℝ,
      objectiveVariationLeft HL0 HL1 HR0 HR1 hA m delta rhoA v =
        lambda₀ * momentVariationLeft L R A m delta rhoA v 0 +
        lambda₁ * momentVariationLeft L R A m delta rhoA v 1 +
        lambda₂ * momentVariationLeft L R A m delta rhoA v 2 := by
    intro v
    have h := hLambda v
    rw [dual_fin_three] at h
    simpa [finiteLeftObjectiveJacobianCLM, finiteLeftObjectiveJacobian,
      finiteLeftMomentJacobianCLM, finiteLeftMomentJacobian,
      lambda₀, lambda₁, lambda₂, mul_comm] using h
  exact ⟨lambda₀, lambda₁, lambda₂,
    residual_equations_of_normalized_factorization_left hdelta hrhoA hfactor⟩

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/HalfLineParametric.lean` -/



open Real Set MeasureTheory intervalIntegral
open scoped Topology Interval

namespace LogConcaveClaimI

/-!
# A two-piece exponential density on a right half-line

The five coordinates below are `(A,c,beta,delta,m)`.  Thus the (unnormalized)
density is

`exp (c + beta*x)` on `[A,m]` and
`exp (c + beta*x - delta*(x-m))` on `[m,+infinity)`.

The infinite integral is differentiated on a fixed tail.  A compact interval
correction then moves its lower endpoint.  This avoids any appeal to a
Leibniz rule with an endpoint at infinity.
-/

abbrev HalfLineParam := Fin 5 → ℝ

def halfLineCoord (i : Fin 5) : HalfLineParam →L[ℝ] ℝ :=
  ContinuousLinearMap.proj i

@[simp] lemma halfLineCoord_apply (i : Fin 5) (p : HalfLineParam) :
    halfLineCoord i p = p i := rfl

def halfLineLeftExponent (p : HalfLineParam) (x : ℝ) : ℝ :=
  p 1 + p 2 * x

def halfLineRightExponent (p : HalfLineParam) (x : ℝ) : ℝ :=
  p 1 + p 2 * x - p 3 * (x - p 4)

def halfLineLeftIntegrand (q : ℝ → ℝ) (p : HalfLineParam) (x : ℝ) : ℝ :=
  q x * exp (halfLineLeftExponent p x)

def halfLineRightIntegrand (q : ℝ → ℝ) (p : HalfLineParam) (x : ℝ) : ℝ :=
  q x * exp (halfLineRightExponent p x)

def halfLineLeftIntegrandFDeriv (q : ℝ → ℝ) (p : HalfLineParam) (x : ℝ) :
    HalfLineParam →L[ℝ] ℝ :=
  (halfLineCoord 1).smulRight (halfLineLeftIntegrand q p x) +
    (halfLineCoord 2).smulRight (x * halfLineLeftIntegrand q p x)

def halfLineRightIntegrandFDeriv (q : ℝ → ℝ) (p : HalfLineParam) (x : ℝ) :
    HalfLineParam →L[ℝ] ℝ :=
  (halfLineCoord 1).smulRight (halfLineRightIntegrand q p x) +
    (halfLineCoord 2).smulRight (x * halfLineRightIntegrand q p x) -
    (halfLineCoord 3).smulRight ((x - p 4) * halfLineRightIntegrand q p x) +
    (halfLineCoord 4).smulRight (p 3 * halfLineRightIntegrand q p x)

lemma continuous_uncurry_halfLineLeftIntegrand {q : ℝ → ℝ} (hq : Continuous q) :
    Continuous (Function.uncurry (halfLineLeftIntegrand q)) := by
  unfold halfLineLeftIntegrand halfLineLeftExponent
  fun_prop

lemma continuous_uncurry_halfLineRightIntegrand {q : ℝ → ℝ} (hq : Continuous q) :
    Continuous (Function.uncurry (halfLineRightIntegrand q)) := by
  unfold halfLineRightIntegrand halfLineRightExponent
  fun_prop

lemma continuous_uncurry_halfLineLeftIntegrandFDeriv {q : ℝ → ℝ}
    (hq : Continuous q) :
    Continuous (Function.uncurry (halfLineLeftIntegrandFDeriv q)) := by
  unfold halfLineLeftIntegrandFDeriv halfLineLeftIntegrand halfLineLeftExponent
    halfLineCoord
  fun_prop

lemma continuous_uncurry_halfLineRightIntegrandFDeriv {q : ℝ → ℝ}
    (hq : Continuous q) :
    Continuous (Function.uncurry (halfLineRightIntegrandFDeriv q)) := by
  unfold halfLineRightIntegrandFDeriv halfLineRightIntegrand halfLineRightExponent
    halfLineCoord
  fun_prop

lemma hasFDerivAt_halfLineLeftIntegrand (q : ℝ → ℝ) (p : HalfLineParam) (x : ℝ) :
    HasFDerivAt (fun u ↦ halfLineLeftIntegrand q u x)
      (halfLineLeftIntegrandFDeriv q p x) p := by
  have hE : HasFDerivAt (fun u : HalfLineParam ↦ halfLineLeftExponent u x)
      (halfLineCoord 1 + x • halfLineCoord 2) p := by
    unfold halfLineLeftExponent
    fun_prop
  have h := hE.exp.const_mul (q x)
  apply h.congr_fderiv
  ext v
  simp [halfLineLeftIntegrandFDeriv, halfLineLeftIntegrand, halfLineCoord]
  ring

lemma hasFDerivAt_halfLineRightIntegrand (q : ℝ → ℝ) (p : HalfLineParam) (x : ℝ) :
    HasFDerivAt (fun u ↦ halfLineRightIntegrand q u x)
      (halfLineRightIntegrandFDeriv q p x) p := by
  have hE : HasFDerivAt (fun u : HalfLineParam ↦ halfLineRightExponent u x)
      (halfLineCoord 1 + x • halfLineCoord 2 -
        (x - p 4) • halfLineCoord 3 + p 3 • halfLineCoord 4) p := by
    have hraw := ((halfLineCoord 1).hasFDerivAt.add
      ((halfLineCoord 2).hasFDerivAt.mul_const x)).sub
        ((halfLineCoord 3).hasFDerivAt.mul
          ((hasFDerivAt_const x p).sub (halfLineCoord 4).hasFDerivAt))
    have hsame : HasFDerivAt (fun u : HalfLineParam ↦ halfLineRightExponent u x)
        _ p := hraw.congr_of_eventuallyEq (by
      filter_upwards [] with u
      rfl)
    apply hsame.congr_fderiv
    ext v
    simp [halfLineCoord]
    ring
  have h := hE.exp.const_mul (q x)
  apply h.congr_fderiv
  ext v
  simp [halfLineRightIntegrandFDeriv, halfLineRightIntegrand, halfLineCoord]
  ring

def halfLineLeftIntegral (q : ℝ → ℝ) (p : HalfLineParam) : ℝ :=
  ∫ x in p 0..p 4, halfLineLeftIntegrand q p x

def halfLineRightIntegral (q : ℝ → ℝ) (p : HalfLineParam) : ℝ :=
  ∫ x in Ioi (p 4), halfLineRightIntegrand q p x

def halfLineIntegral (q : ℝ → ℝ) (p : HalfLineParam) : ℝ :=
  halfLineLeftIntegral q p + halfLineRightIntegral q p

def halfLineRightTail (q : ℝ → ℝ) (r : ℝ) (p : HalfLineParam) : ℝ :=
  ∫ x in Ioi r, halfLineRightIntegrand q p x

def halfLineRightCorrection (q : ℝ → ℝ) (r : ℝ) (p : HalfLineParam) : ℝ :=
  ∫ x in r..p 4, halfLineRightIntegrand q p x

/-- The exact domination assumptions needed for strict differentiation on a
fixed infinite tail.  In applications they follow from `p 2 - p 3 < 0` and
an exponential-tail bound for `q`. -/
def HasRightTailDomination (q : ℝ → ℝ) (r : ℝ) (p : HalfLineParam) : Prop :=
  ∃ U : Set HalfLineParam, ∃ bound : ℝ → ℝ,
    IsOpen U ∧ p ∈ U ∧
    Integrable bound (volume.restrict (Ioi r)) ∧
    (∀ u ∈ U, Integrable (halfLineRightIntegrand q u)
      (volume.restrict (Ioi r))) ∧
    ∀ᵐ x ∂(volume.restrict (Ioi r)), ∀ u ∈ U,
      ‖halfLineRightIntegrandFDeriv q u x‖ ≤ bound x

def halfLineLeftIntegralFDerivRaw (q : ℝ → ℝ) (p : HalfLineParam) :
    HalfLineParam →L[ℝ] ℝ :=
  (((∫ x in p 0..p 4, halfLineLeftIntegrandFDeriv q p x).coprod
      (LogConcaveExtremum.ParametricInterval.endpointFDeriv
        (halfLineLeftIntegrand q) p (p 0) (p 4))) ∘L
    ((ContinuousLinearMap.id ℝ HalfLineParam).prod
      ((halfLineCoord 0).prod (halfLineCoord 4))))

def halfLineRightTailFDeriv (q : ℝ → ℝ) (r : ℝ) (p : HalfLineParam) :
    HalfLineParam →L[ℝ] ℝ :=
  ∫ x in Ioi r, halfLineRightIntegrandFDeriv q p x

def halfLineRightCorrectionFDerivRaw
    (q : ℝ → ℝ) (r : ℝ) (p : HalfLineParam) : HalfLineParam →L[ℝ] ℝ :=
  (((∫ x in r..p 4, halfLineRightIntegrandFDeriv q p x).coprod
      (LogConcaveExtremum.ParametricInterval.endpointFDeriv
        (halfLineRightIntegrand q) p r (p 4))) ∘L
    ((ContinuousLinearMap.id ℝ HalfLineParam).prod
      ((0 : HalfLineParam →L[ℝ] ℝ).prod (halfLineCoord 4))))

def halfLineIntegralFDerivRaw
    (q : ℝ → ℝ) (r : ℝ) (p : HalfLineParam) : HalfLineParam →L[ℝ] ℝ :=
  halfLineLeftIntegralFDerivRaw q p + halfLineRightTailFDeriv q r p -
    halfLineRightCorrectionFDerivRaw q r p

lemma hasStrictFDerivAt_halfLineLeftIntegral {q : ℝ → ℝ} (hq : Continuous q)
    (p : HalfLineParam) :
    HasStrictFDerivAt (halfLineLeftIntegral q) (halfLineLeftIntegralFDerivRaw q p) p := by
  exact LogConcaveExtremum.ParametricInterval.hasStrictFDerivAt_movingIntervalIntegral_of_continuous
    (F := halfLineLeftIntegrand q) (F' := halfLineLeftIntegrandFDeriv q)
    (A := fun u : HalfLineParam ↦ u 0) (B := fun u : HalfLineParam ↦ u 4)
    (p₀ := p) (A' := halfLineCoord 0) (B' := halfLineCoord 4)
    (continuous_uncurry_halfLineLeftIntegrand hq)
    (continuous_uncurry_halfLineLeftIntegrandFDeriv hq)
    (hasFDerivAt_halfLineLeftIntegrand q)
    (halfLineCoord 0).hasStrictFDerivAt
    (halfLineCoord 4).hasStrictFDerivAt

lemma hasStrictFDerivAt_halfLineRightTail {q : ℝ → ℝ} (hq : Continuous q)
    {r : ℝ} {p : HalfLineParam} (hdom : HasRightTailDomination q r p) :
    HasStrictFDerivAt (halfLineRightTail q r) (halfLineRightTailFDeriv q r p) p := by
  rcases hdom with ⟨U, bound, hU, hpU, hbound, hint, hderiv⟩
  exact LogConcaveExtremum.ParametricInterval.hasStrictFDerivAt_integral_of_dominated
    (F := halfLineRightIntegrand q)
    (F' := halfLineRightIntegrandFDeriv q)
    (x₀ := p) (U := U) (bound := bound)
    hU hpU
    (fun u hu ↦ (continuous_uncurry_halfLineRightIntegrand hq).uncurry_left u
      |>.aestronglyMeasurable)
    hint
    (fun u hu ↦ (continuous_uncurry_halfLineRightIntegrandFDeriv hq).uncurry_left u
      |>.aestronglyMeasurable)
    hderiv hbound
    (Filter.Eventually.of_forall fun x u hu ↦ hasFDerivAt_halfLineRightIntegrand q u x)
    (Filter.Eventually.of_forall fun x ↦
      (continuous_uncurry_halfLineRightIntegrandFDeriv hq).uncurry_right x |>.continuousAt)

lemma hasStrictFDerivAt_halfLineRightCorrection {q : ℝ → ℝ} (hq : Continuous q)
    (r : ℝ) (p : HalfLineParam) :
    HasStrictFDerivAt (halfLineRightCorrection q r)
      (halfLineRightCorrectionFDerivRaw q r p) p := by
  exact LogConcaveExtremum.ParametricInterval.hasStrictFDerivAt_movingIntervalIntegral_of_continuous
    (F := halfLineRightIntegrand q) (F' := halfLineRightIntegrandFDeriv q)
    (A := fun _ : HalfLineParam ↦ r) (B := fun u : HalfLineParam ↦ u 4)
    (p₀ := p) (A' := 0) (B' := halfLineCoord 4)
    (continuous_uncurry_halfLineRightIntegrand hq)
    (continuous_uncurry_halfLineRightIntegrandFDeriv hq)
    (hasFDerivAt_halfLineRightIntegrand q)
    (hasStrictFDerivAt_const r p)
    (halfLineCoord 4).hasStrictFDerivAt

lemma integrableOn_Ioi_of_continuous_of_integrableOn_Ioi
    {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} (hf : Continuous f) {a b : ℝ}
    (hb : IntegrableOn f (Ioi b)) : IntegrableOn f (Ioi a) := by
  by_cases hba : b ≤ a
  · exact hb.mono_set (Ioi_subset_Ioi hba)
  · have hab : a ≤ b := le_of_not_ge hba
    rw [← Ioc_union_Ioi_eq_Ioi hab]
    exact (hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self).union hb

lemma halfLineRightIntegral_eq_tail_sub_correction
    {q : ℝ → ℝ} (hq : Continuous q) {r : ℝ} {p : HalfLineParam}
    (htail : IntegrableOn (halfLineRightIntegrand q p) (Ioi r)) :
    halfLineRightIntegral q p =
      halfLineRightTail q r p - halfLineRightCorrection q r p := by
  have hm : IntegrableOn (halfLineRightIntegrand q p) (Ioi (p 4)) :=
    integrableOn_Ioi_of_continuous_of_integrableOn_Ioi
      ((continuous_uncurry_halfLineRightIntegrand hq).uncurry_left p) htail
  have hadd := intervalIntegral.integral_interval_add_Ioi'
    (((continuous_uncurry_halfLineRightIntegrand hq).uncurry_left p).intervalIntegrable
      r (p 4)) hm
  unfold halfLineRightIntegral halfLineRightTail halfLineRightCorrection
  linarith

theorem hasStrictFDerivAt_halfLineIntegral_raw {q : ℝ → ℝ} (hq : Continuous q)
    {r : ℝ} {p : HalfLineParam} (hslope : p 2 - p 3 < 0)
    (hdom : HasRightTailDomination q r p) :
    HasStrictFDerivAt (halfLineIntegral q) (halfLineIntegralFDerivRaw q r p) p := by
  rcases hdom with ⟨U, bound, hU, hpU, hbound, hint, hderiv⟩
  have htail := hasStrictFDerivAt_halfLineRightTail hq
    (⟨U, bound, hU, hpU, hbound, hint, hderiv⟩ : HasRightTailDomination q r p)
  have hdecomp := (hasStrictFDerivAt_halfLineLeftIntegral hq p).add
    (htail.sub (hasStrictFDerivAt_halfLineRightCorrection hq r p))
  have hdecomp' := hdecomp.congr_fderiv (show
      halfLineLeftIntegralFDerivRaw q p +
          (halfLineRightTailFDeriv q r p - halfLineRightCorrectionFDerivRaw q r p) =
        halfLineIntegralFDerivRaw q r p by
      rw [halfLineIntegralFDerivRaw, add_sub_assoc])
  apply hdecomp'.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hpU] with u hu
  unfold halfLineIntegral
  rw [halfLineRightIntegral_eq_tail_sub_correction hq (hint u hu)]
  rfl

def halfLineLeftMoment (p : HalfLineParam) (n : ℕ) : ℝ :=
  halfLineLeftIntegral (fun x ↦ x ^ n) p

def halfLineRightMoment (p : HalfLineParam) (n : ℕ) : ℝ :=
  halfLineRightIntegral (fun x ↦ x ^ n) p

def halfLineIntegralFDerivKKT (q : ℝ → ℝ) (p : HalfLineParam) :
    HalfLineParam →L[ℝ] ℝ :=
  finiteLeftObjectiveJacobianCLM
    (halfLineLeftIntegral q p)
    (halfLineLeftIntegral (fun x ↦ x * q x) p)
    (halfLineRightIntegral q p)
    (halfLineRightIntegral (fun x ↦ x * q x) p)
    (q (p 0)) (p 4) (p 3) (-exp (halfLineLeftExponent p (p 0)))

lemma integrable_halfLineRightIntegrandFDeriv_fixed
    {q : ℝ → ℝ} (hq : Continuous q) {r : ℝ} {p : HalfLineParam}
    (hdom : HasRightTailDomination q r p) :
    Integrable (halfLineRightIntegrandFDeriv q p)
      (volume.restrict (Ioi r)) := by
  rcases hdom with ⟨U, bound, hU, hpU, hbound, hint, hderiv⟩
  apply hbound.mono'
  · exact (continuous_uncurry_halfLineRightIntegrandFDeriv hq).uncurry_left p
      |>.aestronglyMeasurable
  · filter_upwards [hderiv] with x hx
    exact hx p hpU

lemma halfLineRightFDerivIntegral_eq_tail_sub_correction
    {q : ℝ → ℝ} (hq : Continuous q) {r : ℝ} {p : HalfLineParam}
    (hdom : HasRightTailDomination q r p) :
    (∫ x in Ioi (p 4), halfLineRightIntegrandFDeriv q p x) =
      (∫ x in Ioi r, halfLineRightIntegrandFDeriv q p x) -
        ∫ x in r..p 4, halfLineRightIntegrandFDeriv q p x := by
  have hfixed := integrable_halfLineRightIntegrandFDeriv_fixed hq hdom
  have hm : IntegrableOn (halfLineRightIntegrandFDeriv q p) (Ioi (p 4)) :=
    integrableOn_Ioi_of_continuous_of_integrableOn_Ioi
      ((continuous_uncurry_halfLineRightIntegrandFDeriv hq).uncurry_left p) hfixed
  have hadd := intervalIntegral.integral_interval_add_Ioi'
    (((continuous_uncurry_halfLineRightIntegrandFDeriv hq).uncurry_left p).intervalIntegrable
      r (p 4)) hm
  rw [eq_sub_iff_add_eq]
  simpa only [add_comm] using hadd

lemma halfLineLeftIntegral_mul (q : ℝ → ℝ) (p : HalfLineParam) :
    halfLineLeftIntegral (fun x ↦ x * q x) p =
      ∫ x in p 0..p 4, x * halfLineLeftIntegrand q p x := by
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [halfLineLeftIntegrand]
  ring

lemma halfLineRightIntegral_mul (q : ℝ → ℝ) (p : HalfLineParam) :
    halfLineRightIntegral (fun x ↦ x * q x) p =
      ∫ x in Ioi (p 4), x * halfLineRightIntegrand q p x := by
  unfold halfLineRightIntegral halfLineRightIntegrand
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  ring

lemma halfLineIntegralFDerivRaw_eq_KKT {q : ℝ → ℝ} (hq : Continuous q)
    {r : ℝ} {p : HalfLineParam} (hdom : HasRightTailDomination q r p) :
    halfLineIntegralFDerivRaw q r p = halfLineIntegralFDerivKKT q p := by
  apply ContinuousLinearMap.ext
  intro v
  rcases hdom with ⟨U, bound, hU, hpU, hbound, hint, hderiv⟩
  let hDom : HasRightTailDomination q r p :=
    ⟨U, bound, hU, hpU, hbound, hint, hderiv⟩
  have hLi : IntervalIntegrable (halfLineLeftIntegrandFDeriv q p)
      volume (p 0) (p 4) :=
    ((continuous_uncurry_halfLineLeftIntegrandFDeriv hq).uncurry_left p)
      |>.intervalIntegrable _ _
  have hRic : IntervalIntegrable (halfLineRightIntegrandFDeriv q p)
      volume r (p 4) :=
    ((continuous_uncurry_halfLineRightIntegrandFDeriv hq).uncurry_left p)
      |>.intervalIntegrable _ _
  have hRifixed : Integrable (halfLineRightIntegrandFDeriv q p)
      (volume.restrict (Ioi r)) :=
    integrable_halfLineRightIntegrandFDeriv_fixed hq hDom
  have hRi : Integrable (halfLineRightIntegrandFDeriv q p)
      (volume.restrict (Ioi (p 4))) :=
    integrableOn_Ioi_of_continuous_of_integrableOn_Ioi
      ((continuous_uncurry_halfLineRightIntegrandFDeriv hq).uncurry_left p) hRifixed
  have hRc : Continuous (halfLineRightIntegrand q p) :=
    (continuous_uncurry_halfLineRightIntegrand hq).uncurry_left p
  have hR0fixed : Integrable (halfLineRightIntegrand q p)
      (volume.restrict (Ioi r)) := hint p hpU
  have hR0 : Integrable (halfLineRightIntegrand q p)
      (volume.restrict (Ioi (p 4))) :=
    integrableOn_Ioi_of_continuous_of_integrableOn_Ioi hRc hR0fixed
  let eBeta : HalfLineParam := Pi.single (M := fun _ : Fin 5 ↦ ℝ) 2 1
  have hR1raw := hRi.apply_continuousLinearMap eBeta
  have hR1 : Integrable (fun x ↦ x * halfLineRightIntegrand q p x)
      (volume.restrict (Ioi (p 4))) := by
    apply hR1raw.congr
    filter_upwards [] with x
    simp [eBeta, halfLineRightIntegrandFDeriv, halfLineCoord]
  have hRxm : Integrable (fun x ↦ (x - p 4) * halfLineRightIntegrand q p x)
      (volume.restrict (Ioi (p 4))) := by
    have := hR1.sub (hR0.const_mul (p 4))
    apply this.congr
    filter_upwards [] with x
    change x * halfLineRightIntegrand q p x -
      p 4 * halfLineRightIntegrand q p x = _
    ring
  have hL0 : IntervalIntegrable (halfLineLeftIntegrand q p) volume (p 0) (p 4) :=
    ((continuous_uncurry_halfLineLeftIntegrand hq).uncurry_left p)
      |>.intervalIntegrable _ _
  have hL1 : IntervalIntegrable (fun x ↦ x * halfLineLeftIntegrand q p x)
      volume (p 0) (p 4) :=
    (continuous_id.mul
      ((continuous_uncurry_halfLineLeftIntegrand hq).uncurry_left p))
      |>.intervalIntegrable _ _
  have hLint :
      (∫ x in p 0..p 4,
        v 1 * halfLineLeftIntegrand q p x +
          v 2 * (x * halfLineLeftIntegrand q p x)) =
        v 1 * halfLineLeftIntegral q p +
          v 2 * halfLineLeftIntegral (fun x ↦ x * q x) p := by
    rw [intervalIntegral.integral_add (hL0.const_mul (v 1))
      (hL1.const_mul (v 2)), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, ← halfLineLeftIntegral_mul]
    rfl
  have hRxmIntegral :
      (∫ x in Ioi (p 4), (x - p 4) * halfLineRightIntegrand q p x) =
        halfLineRightIntegral (fun x ↦ x * q x) p -
          p 4 * halfLineRightIntegral q p := by
    calc
      (∫ x in Ioi (p 4), (x - p 4) * halfLineRightIntegrand q p x) =
          ∫ x in Ioi (p 4),
            x * halfLineRightIntegrand q p x -
              p 4 * halfLineRightIntegrand q p x := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards [] with x
                ring
      _ = (∫ x in Ioi (p 4), x * halfLineRightIntegrand q p x) -
          ∫ x in Ioi (p 4), p 4 * halfLineRightIntegrand q p x :=
            MeasureTheory.integral_sub hR1 (hR0.const_mul (p 4))
      _ = halfLineRightIntegral (fun x ↦ x * q x) p -
          p 4 * halfLineRightIntegral q p := by
            rw [MeasureTheory.integral_const_mul, ← halfLineRightIntegral_mul]
            rfl
  have hRint :
      (∫ x in Ioi (p 4),
        v 1 * halfLineRightIntegrand q p x +
          v 2 * (x * halfLineRightIntegrand q p x) -
          v 3 * ((x - p 4) * halfLineRightIntegrand q p x) +
          v 4 * (p 3 * halfLineRightIntegrand q p x)) =
        v 1 * halfLineRightIntegral q p +
          v 2 * halfLineRightIntegral (fun x ↦ x * q x) p -
          v 3 * (halfLineRightIntegral (fun x ↦ x * q x) p -
            p 4 * halfLineRightIntegral q p) +
          v 4 * (p 3 * halfLineRightIntegral q p) := by
    calc
      (∫ x in Ioi (p 4),
        v 1 * halfLineRightIntegrand q p x +
          v 2 * (x * halfLineRightIntegrand q p x) -
          v 3 * ((x - p 4) * halfLineRightIntegrand q p x) +
          v 4 * (p 3 * halfLineRightIntegrand q p x)) =
          (∫ x in Ioi (p 4),
            v 1 * halfLineRightIntegrand q p x +
              v 2 * (x * halfLineRightIntegrand q p x) -
              v 3 * ((x - p 4) * halfLineRightIntegrand q p x)) +
          ∫ x in Ioi (p 4),
            v 4 * (p 3 * halfLineRightIntegrand q p x) := by
              exact MeasureTheory.integral_add
                (((hR0.const_mul (v 1)).add (hR1.const_mul (v 2))).sub
                  (hRxm.const_mul (v 3)))
                ((hR0.const_mul (p 3)).const_mul (v 4))
      _ = ((∫ x in Ioi (p 4),
            v 1 * halfLineRightIntegrand q p x +
              v 2 * (x * halfLineRightIntegrand q p x)) -
            ∫ x in Ioi (p 4),
              v 3 * ((x - p 4) * halfLineRightIntegrand q p x)) +
          ∫ x in Ioi (p 4),
            v 4 * (p 3 * halfLineRightIntegrand q p x) := by
              have hs := MeasureTheory.integral_sub
                ((hR0.const_mul (v 1)).add (hR1.const_mul (v 2)))
                (hRxm.const_mul (v 3))
              exact congrArg (fun z ↦ z +
                ∫ x in Ioi (p 4),
                  v 4 * (p 3 * halfLineRightIntegrand q p x)) hs
      _ = (((∫ x in Ioi (p 4), v 1 * halfLineRightIntegrand q p x) +
            ∫ x in Ioi (p 4),
              v 2 * (x * halfLineRightIntegrand q p x)) -
            ∫ x in Ioi (p 4),
              v 3 * ((x - p 4) * halfLineRightIntegrand q p x)) +
          ∫ x in Ioi (p 4),
            v 4 * (p 3 * halfLineRightIntegrand q p x) := by
              have ha := MeasureTheory.integral_add (hR0.const_mul (v 1))
                (hR1.const_mul (v 2))
              exact congrArg (fun z ↦ (z -
                ∫ x in Ioi (p 4),
                  v 3 * ((x - p 4) * halfLineRightIntegrand q p x)) +
                ∫ x in Ioi (p 4),
                  v 4 * (p 3 * halfLineRightIntegrand q p x)) ha
      _ = _ := by
        simp only [MeasureTheory.integral_const_mul]
        rw [← halfLineRightIntegral_mul, hRxmIntegral]
        simp only [halfLineRightIntegral]
  have hmatch : halfLineLeftIntegrand q p (p 4) =
      halfLineRightIntegrand q p (p 4) := by
    simp only [halfLineLeftIntegrand, halfLineRightIntegrand,
      halfLineLeftExponent, halfLineRightExponent]
    ring_nf
  have hsplit := halfLineRightFDerivIntegral_eq_tail_sub_correction hq hDom
  have hsplitv := congrArg (fun T : HalfLineParam →L[ℝ] ℝ ↦ T v) hsplit
  simp only [ContinuousLinearMap.sub_apply] at hsplitv
  rw [ContinuousLinearMap.integral_apply hRi v,
    ContinuousLinearMap.integral_apply hRifixed v,
    ContinuousLinearMap.intervalIntegral_apply hRic v] at hsplitv
  simp [halfLineRightIntegrandFDeriv, halfLineCoord] at hsplitv
  simp only [halfLineIntegralFDerivRaw, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, halfLineLeftIntegralFDerivRaw,
    halfLineRightTailFDeriv, halfLineRightCorrectionFDerivRaw,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]
  rw [ContinuousLinearMap.intervalIntegral_apply hLi v,
    ContinuousLinearMap.integral_apply hRifixed v,
    ContinuousLinearMap.intervalIntegral_apply hRic v]
  simp [LogConcaveExtremum.ParametricInterval.endpointFDeriv,
    halfLineLeftIntegrandFDeriv, halfLineRightIntegrandFDeriv, halfLineCoord]
  have hcombine :
      ((∫ x in p 0..p 4,
            v 1 * halfLineLeftIntegrand q p x +
              v 2 * (x * halfLineLeftIntegrand q p x)) +
            (v 4 * halfLineLeftIntegrand q p (p 4) -
              v 0 * halfLineLeftIntegrand q p (p 0)) +
          ∫ x in Ioi r,
            v 1 * halfLineRightIntegrand q p x +
              v 2 * (x * halfLineRightIntegrand q p x) -
              v 3 * ((x - p 4) * halfLineRightIntegrand q p x) +
              v 4 * (p 3 * halfLineRightIntegrand q p x)) -
        ((∫ x in r..p 4,
            v 1 * halfLineRightIntegrand q p x +
              v 2 * (x * halfLineRightIntegrand q p x) -
              v 3 * ((x - p 4) * halfLineRightIntegrand q p x) +
              v 4 * (p 3 * halfLineRightIntegrand q p x)) +
          v 4 * halfLineRightIntegrand q p (p 4)) =
      ((∫ x in p 0..p 4,
            v 1 * halfLineLeftIntegrand q p x +
              v 2 * (x * halfLineLeftIntegrand q p x)) +
            (v 4 * halfLineLeftIntegrand q p (p 4) -
              v 0 * halfLineLeftIntegrand q p (p 0)) +
          ∫ x in Ioi (p 4),
            v 1 * halfLineRightIntegrand q p x +
              v 2 * (x * halfLineRightIntegrand q p x) -
              v 3 * ((x - p 4) * halfLineRightIntegrand q p x) +
              v 4 * (p 3 * halfLineRightIntegrand q p x)) -
        v 4 * halfLineRightIntegrand q p (p 4) := by
    linarith [hsplitv]
  rw [hcombine, hLint, hRint, hmatch]
  change _ = objectiveVariationLeft
    (halfLineLeftIntegral q p)
    (halfLineLeftIntegral (fun x ↦ x * q x) p)
    (halfLineRightIntegral q p)
    (halfLineRightIntegral (fun x ↦ x * q x) p)
    (q (p 0)) (p 4) (p 3) (-exp (halfLineLeftExponent p (p 0))) v
  simp only [objectiveVariationLeft]
  simp only [halfLineLeftIntegrand, halfLineRightIntegrand,
    halfLineLeftExponent, halfLineRightExponent]
  ring

theorem hasStrictFDerivAt_halfLineIntegral {q : ℝ → ℝ} (hq : Continuous q)
    {r : ℝ} {p : HalfLineParam} (hslope : p 2 - p 3 < 0)
    (hdom : HasRightTailDomination q r p) :
    HasStrictFDerivAt (halfLineIntegral q) (halfLineIntegralFDerivKKT q p) p := by
  exact (hasStrictFDerivAt_halfLineIntegral_raw hq hslope hdom).congr_fderiv
    (halfLineIntegralFDerivRaw_eq_KKT hq hdom)

def halfLineMomentMap (p : HalfLineParam) (k : Fin 3) : ℝ :=
  halfLineIntegral (fun x ↦ x ^ k.val) p

def halfLineMomentFDerivPi (p : HalfLineParam) :
    HalfLineParam →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun k : Fin 3 ↦
    halfLineIntegralFDerivKKT (fun x ↦ x ^ k.val) p)

lemma halfLineLeftIntegral_mul_pow (p : HalfLineParam) (n : ℕ) :
    halfLineLeftIntegral (fun x ↦ x * x ^ n) p =
      halfLineLeftMoment p (n + 1) := by
  unfold halfLineLeftMoment halfLineLeftIntegral halfLineLeftIntegrand
  apply intervalIntegral.integral_congr
  intro x hx
  change (x * x ^ n) * exp (halfLineLeftExponent p x) =
    x ^ (n + 1) * exp (halfLineLeftExponent p x)
  rw [pow_succ]
  ring

lemma halfLineRightIntegral_mul_pow (p : HalfLineParam) (n : ℕ) :
    halfLineRightIntegral (fun x ↦ x * x ^ n) p =
      halfLineRightMoment p (n + 1) := by
  unfold halfLineRightMoment halfLineRightIntegral halfLineRightIntegrand
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  change (x * x ^ n) * exp (halfLineRightExponent p x) =
    x ^ (n + 1) * exp (halfLineRightExponent p x)
  rw [pow_succ]
  ring

lemma hasStrictFDerivAt_halfLineMomentMap_pi
    {r : ℝ} {p : HalfLineParam} (hslope : p 2 - p 3 < 0)
    (hdom : ∀ k : Fin 3,
      HasRightTailDomination (fun x ↦ x ^ k.val) r p) :
    HasStrictFDerivAt halfLineMomentMap (halfLineMomentFDerivPi p) p := by
  apply hasStrictFDerivAt_pi.mpr
  intro k
  exact hasStrictFDerivAt_halfLineIntegral (continuous_id.pow k.val)
    hslope (hdom k)

lemma halfLineMomentFDerivPi_eq_KKT (p : HalfLineParam) :
    halfLineMomentFDerivPi p =
      finiteLeftMomentJacobianCLM
        (halfLineLeftMoment p) (halfLineRightMoment p)
        (p 0) (p 4) (p 3) (-exp (halfLineLeftExponent p (p 0))) := by
  apply ContinuousLinearMap.ext
  intro v
  ext k
  simp only [halfLineMomentFDerivPi, ContinuousLinearMap.pi_apply]
  change objectiveVariationLeft
      (halfLineLeftMoment p k.val)
      (halfLineLeftIntegral (fun x ↦ x * x ^ k.val) p)
      (halfLineRightMoment p k.val)
      (halfLineRightIntegral (fun x ↦ x * x ^ k.val) p)
      ((p 0) ^ k.val) (p 4) (p 3)
      (-exp (halfLineLeftExponent p (p 0))) v =
    momentVariationLeft (halfLineLeftMoment p) (halfLineRightMoment p)
      (p 0) (p 4) (p 3) (-exp (halfLineLeftExponent p (p 0))) v k
  rw [halfLineLeftIntegral_mul_pow, halfLineRightIntegral_mul_pow]
  rfl

theorem hasStrictFDerivAt_halfLineMomentMap
    {r : ℝ} {p : HalfLineParam} (hslope : p 2 - p 3 < 0)
    (hdom : ∀ k : Fin 3,
      HasRightTailDomination (fun x ↦ x ^ k.val) r p) :
    HasStrictFDerivAt halfLineMomentMap
      (finiteLeftMomentJacobianCLM
        (halfLineLeftMoment p) (halfLineRightMoment p)
        (p 0) (p 4) (p 3) (-exp (halfLineLeftExponent p (p 0)))) p := by
  exact (hasStrictFDerivAt_halfLineMomentMap_pi hslope hdom).congr_fderiv
    (halfLineMomentFDerivPi_eq_KKT p)


end LogConcaveClaimI

/-! ## Flattened source: `lean_i/GAlphaBounds.lean` -/



open Real

namespace LogConcaveClaimI

lemma gAlpha_nonneg {alpha : ℝ} (halpha : 0 ≤ alpha) (x : ℝ) :
    0 ≤ gAlpha alpha x := by
  unfold gAlpha
  positivity

lemma gAlpha_le_one {alpha : ℝ} (halpha : 0 ≤ alpha) (x : ℝ) :
    gAlpha alpha x ≤ 1 := by
  let y := alpha * |x|
  have hy : 0 ≤ y := mul_nonneg halpha (abs_nonneg x)
  have h := add_one_le_exp y
  have he : 0 < exp (-y) := exp_pos _
  have hm := mul_le_mul_of_nonneg_right h he.le
  calc
    gAlpha alpha x = (y + 1) * exp (-y) := by
      simp [gAlpha, y, add_comm]
    _ ≤ exp y * exp (-y) := hm
    _ = exp (y + -y) := (exp_add y (-y)).symm
    _ = 1 := by simp

lemma abs_gAlpha_le_one {alpha : ℝ} (halpha : 0 ≤ alpha) (x : ℝ) :
    |gAlpha alpha x| ≤ 1 := by
  rw [abs_of_nonneg (gAlpha_nonneg halpha x)]
  exact gAlpha_le_one halpha x

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/TailIntegrability.lean` -/



open Real Set MeasureTheory

namespace LogConcaveClaimI

/-- Every polynomial times a genuinely decaying exponential is integrable
on a right half-line. -/
theorem integrableOn_pow_mul_exp_mul_Ioi
    (n : ℕ) {k : ℝ} (hk : k < 0) (a : ℝ) :
    IntegrableOn (fun x : ℝ ↦ x ^ n * exp (k * x)) (Ioi a) := by
  let t : ℝ := -k / 2
  have ht : t ≠ 0 := by
    dsimp [t]
    linarith
  have hplus : k + t < 0 := by
    dsimp [t]
    linarith
  have hminus : k - t < 0 := by
    dsimp [t]
    linarith
  have hiPlus : Integrable
      (fun x : ℝ ↦ exp ((k + t) * x)) (volume.restrict (Ioi a)) :=
    integrableOn_exp_mul_Ioi hplus a
  have hiMinus : Integrable
      (fun x : ℝ ↦ exp ((k - t) * x)) (volume.restrict (Ioi a)) :=
    integrableOn_exp_mul_Ioi hminus a
  exact ProbabilityTheory.integrable_pow_mul_exp_of_integrable_exp_mul
    (X := fun x : ℝ ↦ x) (v := k) (t := t) ht hiPlus hiMinus n

/-- The left-half-line counterpart. -/
theorem integrableOn_pow_mul_exp_mul_Iio
    (n : ℕ) {k : ℝ} (hk : 0 < k) (a : ℝ) :
    IntegrableOn (fun x : ℝ ↦ x ^ n * exp (k * x)) (Iio a) := by
  let t : ℝ := k / 2
  have ht : t ≠ 0 := by
    dsimp [t]
    linarith
  have hplus : 0 < k + t := by
    dsimp [t]
    linarith
  have hminus : 0 < k - t := by
    dsimp [t]
    linarith
  have hiPlus : Integrable
      (fun x : ℝ ↦ exp ((k + t) * x)) (volume.restrict (Iio a)) :=
    (integrableOn_exp_mul_Iic hplus a).mono_set Iio_subset_Iic_self
  have hiMinus : Integrable
      (fun x : ℝ ↦ exp ((k - t) * x)) (volume.restrict (Iio a)) :=
    (integrableOn_exp_mul_Iic hminus a).mono_set Iio_subset_Iic_self
  exact ProbabilityTheory.integrable_pow_mul_exp_of_integrable_exp_mul
    (X := fun x : ℝ ↦ x) (v := k) (t := t) ht hiPlus hiMinus n

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/TailGAlphaIntegrability.lean` -/



open Real Set MeasureTheory

namespace LogConcaveClaimI

theorem integrableOn_pow_mul_gAlpha_mul_exp_mul_Ioi
    (n : ℕ) {alpha k : ℝ} (halpha : 0 ≤ alpha) (hk : k < 0) (a : ℝ) :
    IntegrableOn
      (fun x : ℝ ↦ x ^ n * gAlpha alpha x * exp (k * x)) (Ioi a) := by
  have h := integrableOn_pow_mul_exp_mul_Ioi n hk a
  change Integrable (fun x : ℝ ↦ x ^ n * exp (k * x))
    (volume.restrict (Ioi a)) at h
  change Integrable (fun x : ℝ ↦ x ^ n * gAlpha alpha x * exp (k * x))
    (volume.restrict (Ioi a))
  apply h.mono
  · exact (((continuous_id.pow n).mul (continuous_gAlpha alpha)).mul
      (continuous_const.mul continuous_id).rexp).aestronglyMeasurable
  · filter_upwards [] with x
    calc
      ‖x ^ n * gAlpha alpha x * exp (k * x)‖ =
          ‖x ^ n * exp (k * x)‖ * ‖gAlpha alpha x‖ := by
            simp only [Real.norm_eq_abs, abs_mul]
            ring_nf
      _ ≤ ‖x ^ n * exp (k * x)‖ * 1 :=
        mul_le_mul_of_nonneg_left (abs_gAlpha_le_one halpha x)
          (norm_nonneg _)
      _ = ‖x ^ n * exp (k * x)‖ := mul_one _

theorem integrableOn_pow_mul_gAlpha_mul_exp_mul_Iio
    (n : ℕ) {alpha k : ℝ} (halpha : 0 ≤ alpha) (hk : 0 < k) (a : ℝ) :
    IntegrableOn
      (fun x : ℝ ↦ x ^ n * gAlpha alpha x * exp (k * x)) (Iio a) := by
  have h := integrableOn_pow_mul_exp_mul_Iio n hk a
  change Integrable (fun x : ℝ ↦ x ^ n * exp (k * x))
    (volume.restrict (Iio a)) at h
  change Integrable (fun x : ℝ ↦ x ^ n * gAlpha alpha x * exp (k * x))
    (volume.restrict (Iio a))
  apply h.mono
  · exact (((continuous_id.pow n).mul (continuous_gAlpha alpha)).mul
      (continuous_const.mul continuous_id).rexp).aestronglyMeasurable
  · filter_upwards [] with x
    calc
      ‖x ^ n * gAlpha alpha x * exp (k * x)‖ =
          ‖x ^ n * exp (k * x)‖ * ‖gAlpha alpha x‖ := by
            simp only [Real.norm_eq_abs, abs_mul]
            ring_nf
      _ ≤ ‖x ^ n * exp (k * x)‖ * 1 :=
        mul_le_mul_of_nonneg_left (abs_gAlpha_le_one halpha x)
          (norm_nonneg _)
      _ = ‖x ^ n * exp (k * x)‖ := mul_one _

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/TailCLMNorm.lean` -/



open Real

namespace LogConcaveClaimI

lemma norm_halfLineRightIntegrandFDeriv_le
    (q : ℝ → ℝ) (p : HalfLineParam) (x : ℝ) :
    ‖halfLineRightIntegrandFDeriv q p x‖ ≤
      |halfLineRightIntegrand q p x| *
        (1 + |x| + |x - p 4| + |p 3|) := by
  let f := halfLineRightIntegrand q p x
  let M := |f| * (1 + |x| + |x - p 4| + |p 3|)
  change ‖halfLineRightIntegrandFDeriv q p x‖ ≤ M
  apply ContinuousLinearMap.opNorm_le_bound _
  · dsimp [M]
    positivity
  · intro v
    have h1 : |v 1| ≤ ‖v‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm v (1 : Fin 5)
    have h2 : |v 2| ≤ ‖v‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm v (2 : Fin 5)
    have h3 : |v 3| ≤ ‖v‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm v (3 : Fin 5)
    have h4 : |v 4| ≤ ‖v‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm v (4 : Fin 5)
    change |v 1 * f + v 2 * (x * f) - v 3 * ((x - p 4) * f) +
      v 4 * (p 3 * f)| ≤ M * ‖v‖
    calc
      |v 1 * f + v 2 * (x * f) - v 3 * ((x - p 4) * f) +
          v 4 * (p 3 * f)| ≤
          |v 1 * f| + |v 2 * (x * f)| + |v 3 * ((x - p 4) * f)| +
            |v 4 * (p 3 * f)| := by
              calc
                _ ≤ |v 1 * f + v 2 * (x * f) - v 3 * ((x - p 4) * f)| +
                    |v 4 * (p 3 * f)| := abs_add_le _ _
                _ ≤ (|v 1 * f + v 2 * (x * f)| +
                    |v 3 * ((x - p 4) * f)|) + |v 4 * (p 3 * f)| := by
                      have hs :
                          |v 1 * f + v 2 * (x * f) -
                              v 3 * ((x - p 4) * f)| ≤
                            |v 1 * f + v 2 * (x * f)| +
                              |v 3 * ((x - p 4) * f)| := by
                        rw [sub_eq_add_neg]
                        simpa only [abs_neg] using
                          (abs_add_le (v 1 * f + v 2 * (x * f))
                            (-(v 3 * ((x - p 4) * f))))
                      linarith [abs_nonneg (v 4 * (p 3 * f))]
                _ ≤ (|v 1 * f| + |v 2 * (x * f)| +
                    |v 3 * ((x - p 4) * f)|) + |v 4 * (p 3 * f)| := by
                      gcongr
                      exact abs_add_le _ _
                _ = _ := by ring
      _ ≤ M * ‖v‖ := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
        dsimp [M]
        have e1 : |v 1| * |f| ≤ ‖v‖ * |f| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg f)
        have e2 : |v 2| * (|x| * |f|) ≤ ‖v‖ * (|x| * |f|) :=
          mul_le_mul_of_nonneg_right h2 (mul_nonneg (abs_nonneg x) (abs_nonneg f))
        have e3 : |v 3| * (|x - p 4| * |f|) ≤
            ‖v‖ * (|x - p 4| * |f|) :=
          mul_le_mul_of_nonneg_right h3
            (mul_nonneg (abs_nonneg _) (abs_nonneg f))
        have e4 : |v 4| * (|p 3| * |f|) ≤ ‖v‖ * (|p 3| * |f|) :=
          mul_le_mul_of_nonneg_right h4
            (mul_nonneg (abs_nonneg _) (abs_nonneg f))
        linarith [e1, e2, e3, e4]

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/TailDomination.lean` -/



open Real Set Filter MeasureTheory

namespace LogConcaveClaimI

/-- A reusable tail-domination constructor.  On a tail beginning to the
right of `1`, any continuous `q` bounded by a fixed power is admissible. -/
theorem hasRightTailDomination_of_abs_le_pow
    (q : ℝ → ℝ) (hqcont : Continuous q) (n : ℕ)
    (p : HalfLineParam) (hslope : p 2 - p 3 < 0)
    (r : ℝ) (hr : 1 ≤ r)
    (hqpow : ∀ x ∈ Ioi r, |q x| ≤ x ^ n) :
    HasRightTailDomination q r p := by
  let s := (p 2 - p 3) / 2
  let C1 := |p 1| + 1
  let C3 := |p 3| + 1
  let C4 := |p 4| + 1
  let C0 := C1 + C3 * C4
  let D := 3 + C3 + C4
  let U : Set HalfLineParam :=
    {u | u 2 - u 3 < s ∧ |u 1| < C1 ∧ |u 3| < C3 ∧ |u 4| < C4}
  let bound : ℝ → ℝ := fun x ↦
    (exp C0 * D) * (x ^ (n + 1) * exp (s * x))
  have hs : s < 0 := by
    dsimp [s]
    linarith
  have hC1 : 0 < C1 := by dsimp [C1]; positivity
  have hC3 : 0 < C3 := by dsimp [C3]; positivity
  have hC4 : 0 < C4 := by dsimp [C4]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hUopen : IsOpen U := by
    have hslopeCont : Continuous (fun u : HalfLineParam ↦ u 2 - u 3) := by fun_prop
    have h1cont : Continuous (fun u : HalfLineParam ↦ |u 1|) := by fun_prop
    have h3cont : Continuous (fun u : HalfLineParam ↦ |u 3|) := by fun_prop
    have h4cont : Continuous (fun u : HalfLineParam ↦ |u 4|) := by fun_prop
    change IsOpen ({u : HalfLineParam | u 2 - u 3 < s} ∩
      ({u : HalfLineParam | |u 1| < C1} ∩
        ({u : HalfLineParam | |u 3| < C3} ∩
          {u : HalfLineParam | |u 4| < C4})))
    exact (isOpen_lt hslopeCont continuous_const).inter
      ((isOpen_lt h1cont continuous_const).inter
        ((isOpen_lt h3cont continuous_const).inter
          (isOpen_lt h4cont continuous_const)))
  have hpU : p ∈ U := by
    change p 2 - p 3 < s ∧ |p 1| < C1 ∧ |p 3| < C3 ∧ |p 4| < C4
    constructor
    · dsimp [s]
      linarith
    · dsimp [C1, C3, C4]
      constructor
      · linarith
      · constructor <;> linarith
  have hbound : Integrable bound (volume.restrict (Ioi r)) := by
    have hbase := integrableOn_pow_mul_exp_mul_Ioi (n + 1) hs r
    have hc := hbase.const_mul (exp C0 * D)
    simpa only [bound] using hc
  have hcommon : ∀ u ∈ U, ∀ x ∈ Ioi r,
      |halfLineRightIntegrand q u x| ≤
          exp C0 * x ^ n * exp (s * x) ∧
      1 + |x| + |x - u 4| + |u 3| ≤ D * x := by
    intro u hu x hx
    change u 2 - u 3 < s ∧ |u 1| < C1 ∧ |u 3| < C3 ∧ |u 4| < C4 at hu
    rcases hu with ⟨hus, hu1, hu3, hu4⟩
    have hx1 : 1 ≤ x := hr.trans hx.le
    have hx0 : 0 ≤ x := le_trans (by norm_num) hx1
    have hexpArg : halfLineRightExponent u x ≤ C0 + s * x := by
      have hsx : (u 2 - u 3) * x ≤ s * x :=
        mul_le_mul_of_nonneg_right hus.le hx0
      have hu1' : u 1 ≤ C1 := (le_abs_self _).trans hu1.le
      have hu34abs : |u 3| * |u 4| ≤ C3 * C4 :=
        mul_le_mul hu3.le hu4.le (abs_nonneg _) hC3.le
      have hu34 : u 3 * u 4 ≤ C3 * C4 := by
        calc
          u 3 * u 4 ≤ |u 3 * u 4| := le_abs_self _
          _ = |u 3| * |u 4| := abs_mul _ _
          _ ≤ C3 * C4 := hu34abs
      dsimp [halfLineRightExponent, C0]
      linarith
    have he : exp (halfLineRightExponent u x) ≤ exp C0 * exp (s * x) := by
      calc
        exp (halfLineRightExponent u x) ≤ exp (C0 + s * x) :=
          (exp_le_exp.mpr hexpArg)
        _ = exp C0 * exp (s * x) := exp_add _ _
    have hq := hqpow x hx
    have hfirst : |halfLineRightIntegrand q u x| ≤
        exp C0 * x ^ n * exp (s * x) := by
      rw [halfLineRightIntegrand, abs_mul, abs_exp]
      have hxn : 0 ≤ x ^ n := pow_nonneg hx0 _
      calc
        |q x| * exp (halfLineRightExponent u x) ≤
            x ^ n * (exp C0 * exp (s * x)) :=
          mul_le_mul hq he (exp_pos _).le hxn
        _ = exp C0 * x ^ n * exp (s * x) := by ring
    have hxu : |x - u 4| ≤ x + |u 4| := by
      calc
        |x - u 4| ≤ |x| + |u 4| := by
          simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-u 4)
        _ = x + |u 4| := by rw [abs_of_nonneg hx0]
    have hsecond : 1 + |x| + |x - u 4| + |u 3| ≤ D * x := by
      rw [abs_of_nonneg hx0]
      have hleft : 1 + x + |x - u 4| + |u 3| ≤
          1 + 2 * x + C4 + C3 := by linarith
      have hright : 1 + 2 * x + C4 + C3 ≤ D * x := by
        dsimp [D]
        nlinarith [mul_nonneg (add_nonneg hC3.le hC4.le) (sub_nonneg.mpr hx1)]
      exact hleft.trans hright
    exact ⟨hfirst, hsecond⟩
  refine ⟨U, bound, hUopen, hpU, hbound, ?_, ?_⟩
  · intro u hu
    apply hbound.mono'
    · exact (continuous_uncurry_halfLineRightIntegrand hqcont).uncurry_left u
        |>.aestronglyMeasurable
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hc := (hcommon u hu x hx).1
      have hx0 : 0 ≤ x := le_trans (by norm_num) (hr.trans hx.le)
      have hfac : 1 ≤ D * x := by
        have hDone : 1 ≤ D := by linarith
        have hmul := mul_le_mul hDone (hr.trans hx.le)
          (by norm_num : (0 : ℝ) ≤ 1) hD.le
        norm_num at hmul ⊢
        exact hmul
      change |halfLineRightIntegrand q u x| ≤ bound x
      dsimp [bound]
      have hnon : 0 ≤ exp C0 * x ^ n * exp (s * x) := by positivity
      calc
        |halfLineRightIntegrand q u x| ≤
            exp C0 * x ^ n * exp (s * x) := hc
        _ ≤ (exp C0 * D) * (x ^ (n + 1) * exp (s * x)) := by
          calc
            exp C0 * x ^ n * exp (s * x) =
                (exp C0 * x ^ n * exp (s * x)) * 1 := by ring
            _ ≤ (exp C0 * x ^ n * exp (s * x)) * (D * x) :=
              mul_le_mul_of_nonneg_left hfac hnon
            _ = (exp C0 * D) * (x ^ (n + 1) * exp (s * x)) := by
              rw [pow_succ]
              ring
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx u hu
    have hc := hcommon u hu x hx
    have hnorm := norm_halfLineRightIntegrandFDeriv_le q u x
    have hx0 : 0 ≤ x := le_trans (by norm_num) (hr.trans hx.le)
    change ‖halfLineRightIntegrandFDeriv q u x‖ ≤ bound x
    dsimp [bound]
    calc
      ‖halfLineRightIntegrandFDeriv q u x‖ ≤
          |halfLineRightIntegrand q u x| *
            (1 + |x| + |x - u 4| + |u 3|) := hnorm
      _ ≤ (exp C0 * x ^ n * exp (s * x)) * (D * x) := by
        exact mul_le_mul hc.1 hc.2 (by positivity)
          (mul_nonneg (mul_nonneg (exp_pos _).le (pow_nonneg hx0 n))
            (exp_pos _).le)
      _ = (exp C0 * D) * (x ^ (n + 1) * exp (s * x)) := by
        rw [pow_succ]
        ring

theorem hasRightTailDomination_pow
    (n : ℕ) (p : HalfLineParam) (hslope : p 2 - p 3 < 0) :
    HasRightTailDomination (fun x : ℝ ↦ x ^ n)
      (max (p 4) 1) p := by
  apply hasRightTailDomination_of_abs_le_pow (fun x : ℝ ↦ x ^ n)
    (continuous_id.pow n) n p hslope (max (p 4) 1) (le_max_right _ _)
  intro x hx
  have hx0 : 0 ≤ x := le_trans (by norm_num) ((le_max_right (p 4) 1).trans hx.le)
  rw [abs_of_nonneg (pow_nonneg hx0 n)]

theorem hasRightTailDomination_gAlpha
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (p : HalfLineParam) (hslope : p 2 - p 3 < 0) :
    HasRightTailDomination (gAlpha alpha) (max (p 4) 1) p := by
  apply hasRightTailDomination_of_abs_le_pow (gAlpha alpha)
    (continuous_gAlpha alpha) 0 p hslope (max (p 4) 1) (le_max_right _ _)
  intro x hx
  simpa only [pow_zero] using abs_gAlpha_le_one halpha x

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/UnboundedContradiction.lean` -/



open Real Set MeasureTheory

namespace LogConcaveClaimI

theorem finite_left_endpoint_contradiction
    {alpha A m lambda₀ lambda₁ lambda₂ : ℝ} {wL wR : ℝ → ℝ}
    (halpha : 0 < alpha) (hAm : A < m)
    (hwL : ContinuousOn wL (Ioo A m)) (hwR : ContinuousOn wR (Ioi m))
    (hwposL : ∀ x ∈ Ioo A m, 0 < wL x) (hwposR : ∀ x ∈ Ioi m, 0 < wR x)
    (hrL : IntegrableOn
      (fun x ↦ residual alpha lambda₀ lambda₁ lambda₂ x * wL x) (Ioo A m) volume)
    (hxrL : IntegrableOn
      (fun x ↦ x * residual alpha lambda₀ lambda₁ lambda₂ x * wL x) (Ioo A m) volume)
    (hrR : IntegrableOn
      (fun x ↦ residual alpha lambda₀ lambda₁ lambda₂ x * wR x) (Ioi m) volume)
    (hxrR : IntegrableOn
      (fun x ↦ x * residual alpha lambda₀ lambda₁ lambda₂ x * wR x) (Ioi m) volume)
    (hL₀ : (∫ x in Ioo A m, residual alpha lambda₀ lambda₁ lambda₂ x * wL x) = 0)
    (hL₁ : (∫ x in Ioo A m, x * residual alpha lambda₀ lambda₁ lambda₂ x * wL x) = 0)
    (hR₀ : (∫ x in Ioi m, residual alpha lambda₀ lambda₁ lambda₂ x * wR x) = 0)
    (hR₁ : (∫ x in Ioi m, x * residual alpha lambda₀ lambda₁ lambda₂ x * wR x) = 0)
    (hendpoint : residual alpha lambda₀ lambda₁ lambda₂ A = 0) : False := by
  let r := residual alpha lambda₀ lambda₁ lambda₂
  have hrc : Continuous r := continuous_residual alpha lambda₀ lambda₁ lambda₂
  obtain ⟨x₁, x₂, hx₁, hx₂, hx₁x₂, hrx₁, hrx₂⟩ :=
    two_zeros_of_weighted_set_moments (openOrderInterval_Ioo hAm) isOpen_Ioo
      hrc.continuousOn hwposL hrL hxrL hL₀ hL₁
  obtain ⟨y₁, y₂, hy₁, hy₂, hy₁y₂, hry₁, hry₂⟩ :=
    two_zeros_of_weighted_set_moments (openOrderInterval_Ioi m) isOpen_Ioi
      hrc.continuousOn hwposR hrR hxrR hR₀ hR₁
  exact no_five_residual_zeros halpha hx₁.1 hx₁x₂ (hx₂.2.trans hy₁) hy₁y₂
    hendpoint hrx₁ hrx₂ hry₁ hry₂

theorem finite_right_endpoint_contradiction
    {alpha m B lambda₀ lambda₁ lambda₂ : ℝ} {wL wR : ℝ → ℝ}
    (halpha : 0 < alpha) (hmB : m < B)
    (hwL : ContinuousOn wL (Iio m)) (hwR : ContinuousOn wR (Ioo m B))
    (hwposL : ∀ x ∈ Iio m, 0 < wL x) (hwposR : ∀ x ∈ Ioo m B, 0 < wR x)
    (hrL : IntegrableOn
      (fun x ↦ residual alpha lambda₀ lambda₁ lambda₂ x * wL x) (Iio m) volume)
    (hxrL : IntegrableOn
      (fun x ↦ x * residual alpha lambda₀ lambda₁ lambda₂ x * wL x) (Iio m) volume)
    (hrR : IntegrableOn
      (fun x ↦ residual alpha lambda₀ lambda₁ lambda₂ x * wR x) (Ioo m B) volume)
    (hxrR : IntegrableOn
      (fun x ↦ x * residual alpha lambda₀ lambda₁ lambda₂ x * wR x) (Ioo m B) volume)
    (hL₀ : (∫ x in Iio m, residual alpha lambda₀ lambda₁ lambda₂ x * wL x) = 0)
    (hL₁ : (∫ x in Iio m, x * residual alpha lambda₀ lambda₁ lambda₂ x * wL x) = 0)
    (hR₀ : (∫ x in Ioo m B, residual alpha lambda₀ lambda₁ lambda₂ x * wR x) = 0)
    (hR₁ : (∫ x in Ioo m B, x * residual alpha lambda₀ lambda₁ lambda₂ x * wR x) = 0)
    (hendpoint : residual alpha lambda₀ lambda₁ lambda₂ B = 0) : False := by
  let r := residual alpha lambda₀ lambda₁ lambda₂
  have hrc : Continuous r := continuous_residual alpha lambda₀ lambda₁ lambda₂
  obtain ⟨x₁, x₂, hx₁, hx₂, hx₁x₂, hrx₁, hrx₂⟩ :=
    two_zeros_of_weighted_set_moments (openOrderInterval_Iio m) isOpen_Iio
      hrc.continuousOn hwposL hrL hxrL hL₀ hL₁
  obtain ⟨y₁, y₂, hy₁, hy₂, hy₁y₂, hry₁, hry₂⟩ :=
    two_zeros_of_weighted_set_moments (openOrderInterval_Ioo hmB) isOpen_Ioo
      hrc.continuousOn hwposR hrR hxrR hR₀ hR₁
  exact no_five_residual_zeros halpha hx₁x₂ (hx₂.trans hy₁.1) hy₁y₂ hy₂.2
    hrx₁ hrx₂ hry₁ hry₂ hendpoint

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/HalfLineClaimI.lean` -/



open Real Set Filter Topology MeasureTheory intervalIntegral
open scoped Topology Interval

namespace LogConcaveClaimI

def finiteLeftKinkDomain : Set HalfLineParam :=
  {p | p 0 < p 4 ∧ 0 < p 3 ∧ p 2 - p 3 < 0}

lemma isOpen_finiteLeftKinkDomain : IsOpen finiteLeftKinkDomain := by
  change IsOpen ({p : HalfLineParam | p 0 < p 4} ∩
    ({p : HalfLineParam | (0 : ℝ) < p 3} ∩
      {p : HalfLineParam | p 2 - p 3 < (0 : ℝ)}))
  exact (isOpen_lt (halfLineCoord 0).continuous (halfLineCoord 4).continuous).inter
    ((isOpen_lt continuous_const (halfLineCoord 3).continuous).inter
      (isOpen_lt ((halfLineCoord 2).continuous.sub (halfLineCoord 3).continuous)
        continuous_const))

lemma finiteLeft_localExtrOn_fiber_of_domain
    {Phi : HalfLineParam → ℝ} {M : HalfLineParam → (Fin 3 → ℝ)}
    {p : HalfLineParam} (hp : p ∈ finiteLeftKinkDomain)
    (h : IsLocalExtrOn Phi ({u | M u = M p} ∩ finiteLeftKinkDomain) p) :
    IsLocalExtrOn Phi {u | M u = M p} p := by
  change IsExtrFilter Phi (𝓝[({u | M u = M p} ∩ finiteLeftKinkDomain)] p) p at h
  change IsExtrFilter Phi (𝓝[{u | M u = M p}] p) p
  rw [nhdsWithin_inter_of_mem'
    (mem_nhdsWithin_of_mem_nhds (isOpen_finiteLeftKinkDomain.mem_nhds hp))] at h
  exact h

def finiteLeftWeight (p : HalfLineParam) (x : ℝ) : ℝ :=
  exp (halfLineLeftExponent p x)

def finiteRightTailWeight (p : HalfLineParam) (x : ℝ) : ℝ :=
  exp (halfLineRightExponent p x)

lemma continuous_finiteLeftWeight (p : HalfLineParam) :
    Continuous (finiteLeftWeight p) := by
  unfold finiteLeftWeight halfLineLeftExponent
  fun_prop

lemma continuous_finiteRightTailWeight (p : HalfLineParam) :
    Continuous (finiteRightTailWeight p) := by
  unfold finiteRightTailWeight halfLineRightExponent
  fun_prop

theorem integrableOn_pow_mul_finiteRightTailWeight
    (p : HalfLineParam) (n : ℕ) (hslope : p 2 - p 3 < 0) (a : ℝ) :
    IntegrableOn (fun x ↦ x ^ n * finiteRightTailWeight p x) (Ioi a) := by
  have h := integrableOn_pow_mul_exp_mul_Ioi n hslope a
  have hc : IntegrableOn
      (fun x ↦ exp (p 1 + p 3 * p 4) *
        (x ^ n * exp ((p 2 - p 3) * x))) (Ioi a) :=
    h.const_mul (exp (p 1 + p 3 * p 4))
  apply hc.congr_fun_ae
  filter_upwards with x
  simp only [finiteRightTailWeight, halfLineRightExponent]
  have he : exp (p 1 + p 3 * p 4) * exp ((p 2 - p 3) * x) =
      exp (p 1 + p 2 * x - p 3 * (x - p 4)) := by
    rw [← exp_add]
    congr 1
    ring
  rw [← he]
  ring

theorem integrableOn_gAlpha_mul_finiteRightTailWeight
    {alpha : ℝ} (halpha : 0 ≤ alpha) (p : HalfLineParam)
    (hslope : p 2 - p 3 < 0) (a : ℝ) :
    IntegrableOn (fun x ↦ gAlpha alpha x * finiteRightTailWeight p x) (Ioi a) := by
  have h := integrableOn_pow_mul_gAlpha_mul_exp_mul_Ioi 0 halpha hslope a
  have hc : IntegrableOn
      (fun x ↦ exp (p 1 + p 3 * p 4) *
        (x ^ 0 * gAlpha alpha x * exp ((p 2 - p 3) * x))) (Ioi a) :=
    h.const_mul (exp (p 1 + p 3 * p 4))
  apply hc.congr_fun_ae
  filter_upwards with x
  simp only [finiteRightTailWeight, halfLineRightExponent, pow_zero, one_mul]
  have he : exp (p 1 + p 3 * p 4) * exp ((p 2 - p 3) * x) =
      exp (p 1 + p 2 * x - p 3 * (x - p 4)) := by
    rw [← exp_add]
    congr 1
    ring
  rw [← he]
  ring

theorem integrableOn_x_gAlpha_mul_finiteRightTailWeight
    {alpha : ℝ} (halpha : 0 ≤ alpha) (p : HalfLineParam)
    (hslope : p 2 - p 3 < 0) (a : ℝ) :
    IntegrableOn
      (fun x ↦ x * gAlpha alpha x * finiteRightTailWeight p x) (Ioi a) := by
  have h := integrableOn_pow_mul_gAlpha_mul_exp_mul_Ioi 1 halpha hslope a
  have hc : IntegrableOn
      (fun x ↦ exp (p 1 + p 3 * p 4) *
        (x ^ 1 * gAlpha alpha x * exp ((p 2 - p 3) * x))) (Ioi a) :=
    h.const_mul (exp (p 1 + p 3 * p 4))
  apply hc.congr_fun_ae
  filter_upwards with x
  simp only [finiteRightTailWeight, halfLineRightExponent, pow_one]
  have he : exp (p 1 + p 3 * p 4) * exp ((p 2 - p 3) * x) =
      exp (p 1 + p 2 * x - p 3 * (x - p 4)) := by
    rw [← exp_add]
    congr 1
    ring
  rw [← he]
  ring

def finiteLeftActualLeftMoment (p : HalfLineParam) (n : ℕ) : ℝ :=
  halfLineLeftIntegral (fun x ↦ x ^ n) p

def finiteLeftActualRightMoment (p : HalfLineParam) (n : ℕ) : ℝ :=
  halfLineRightIntegral (fun x ↦ x ^ n) p

def finiteLeftActualMomentMap (p : HalfLineParam) (k : Fin 3) : ℝ :=
  halfLineIntegral (fun x ↦ x ^ k.val) p

lemma finiteLeftActualLeftMoment_eq_weightedMoment {p : HalfLineParam}
    (hAm : p 0 ≤ p 4) (n : ℕ) :
    finiteLeftActualLeftMoment p n =
      weightedMoment (Ioo (p 0) (p 4)) (finiteLeftWeight p) n := by
  unfold finiteLeftActualLeftMoment halfLineLeftIntegral halfLineLeftIntegrand
    weightedMoment finiteLeftWeight
  rw [intervalIntegral.integral_of_le hAm,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

lemma finiteLeftActualRightMoment_eq_weightedMoment (p : HalfLineParam) (n : ℕ) :
    finiteLeftActualRightMoment p n =
      weightedMoment (Ioi (p 4)) (finiteRightTailWeight p) n := by
  rfl

theorem finiteLeft_moments_quadratic_nondegenerate {p : HalfLineParam}
    (hAm : p 0 < p 4)
    (hintR : ∀ n ≤ 3, IntegrableOn
      (fun x ↦ x ^ n * finiteRightTailWeight p x) (Ioi (p 4))) :
    ∀ a b c : ℝ,
      a * finiteLeftActualLeftMoment p 0 + b * finiteLeftActualLeftMoment p 1 +
          c * finiteLeftActualLeftMoment p 2 = 0 →
      a * finiteLeftActualLeftMoment p 1 + b * finiteLeftActualLeftMoment p 2 +
          c * finiteLeftActualLeftMoment p 3 = 0 →
      a * finiteLeftActualRightMoment p 0 + b * finiteLeftActualRightMoment p 1 +
          c * finiteLeftActualRightMoment p 2 = 0 →
      a * finiteLeftActualRightMoment p 1 + b * finiteLeftActualRightMoment p 2 +
          c * finiteLeftActualRightMoment p 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
  have hbase := separated_moments_quadratic_nondegenerate_two_weights
    (openOrderInterval_Ioo hAm) (openOrderInterval_Ioi (p 4))
    isOpen_Ioo isOpen_Ioi
    (fun _ hx _ hy ↦ hx.2.trans hy)
    (fun x hx ↦ exp_pos _) (fun x hx ↦ exp_pos _)
    (fun n hn ↦ ((continuous_id.pow n).mul
      (continuous_finiteLeftWeight p)).integrableOn_Icc.mono_set Ioo_subset_Icc_self)
    hintR
  intro a b c hL0 hL1 hR0 hR1
  apply hbase a b c
  · change a * weightedMoment (Ioo (p 0) (p 4)) (finiteLeftWeight p) 0 +
        b * weightedMoment (Ioo (p 0) (p 4)) (finiteLeftWeight p) 1 +
        c * weightedMoment (Ioo (p 0) (p 4)) (finiteLeftWeight p) 2 = 0
    rw [← finiteLeftActualLeftMoment_eq_weightedMoment hAm.le 0,
      ← finiteLeftActualLeftMoment_eq_weightedMoment hAm.le 1,
      ← finiteLeftActualLeftMoment_eq_weightedMoment hAm.le 2]
    exact hL0
  · change a * weightedMoment (Ioo (p 0) (p 4)) (finiteLeftWeight p) 1 +
        b * weightedMoment (Ioo (p 0) (p 4)) (finiteLeftWeight p) 2 +
        c * weightedMoment (Ioo (p 0) (p 4)) (finiteLeftWeight p) 3 = 0
    rw [← finiteLeftActualLeftMoment_eq_weightedMoment hAm.le 1,
      ← finiteLeftActualLeftMoment_eq_weightedMoment hAm.le 2,
      ← finiteLeftActualLeftMoment_eq_weightedMoment hAm.le 3]
    exact hL1
  · change a * weightedMoment (Ioi (p 4)) (finiteRightTailWeight p) 0 +
        b * weightedMoment (Ioi (p 4)) (finiteRightTailWeight p) 1 +
        c * weightedMoment (Ioi (p 4)) (finiteRightTailWeight p) 2 = 0
    rw [← finiteLeftActualRightMoment_eq_weightedMoment p 0,
      ← finiteLeftActualRightMoment_eq_weightedMoment p 1,
      ← finiteLeftActualRightMoment_eq_weightedMoment p 2]
    exact hR0
  · change a * weightedMoment (Ioi (p 4)) (finiteRightTailWeight p) 1 +
        b * weightedMoment (Ioi (p 4)) (finiteRightTailWeight p) 2 +
        c * weightedMoment (Ioi (p 4)) (finiteRightTailWeight p) 3 = 0
    rw [← finiteLeftActualRightMoment_eq_weightedMoment p 1,
      ← finiteLeftActualRightMoment_eq_weightedMoment p 2,
      ← finiteLeftActualRightMoment_eq_weightedMoment p 3]
    exact hR1

theorem finiteLeft_moments_quadratic_nondegenerate_of_slope
    {p : HalfLineParam} (hAm : p 0 < p 4) (hslope : p 2 - p 3 < 0) :
    ∀ a b c : ℝ,
      a * finiteLeftActualLeftMoment p 0 + b * finiteLeftActualLeftMoment p 1 +
          c * finiteLeftActualLeftMoment p 2 = 0 →
      a * finiteLeftActualLeftMoment p 1 + b * finiteLeftActualLeftMoment p 2 +
          c * finiteLeftActualLeftMoment p 3 = 0 →
      a * finiteLeftActualRightMoment p 0 + b * finiteLeftActualRightMoment p 1 +
          c * finiteLeftActualRightMoment p 2 = 0 →
      a * finiteLeftActualRightMoment p 1 + b * finiteLeftActualRightMoment p 2 +
          c * finiteLeftActualRightMoment p 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 :=
  finiteLeft_moments_quadratic_nondegenerate hAm
    (fun n hn ↦ integrableOn_pow_mul_finiteRightTailWeight p n hslope (p 4))

lemma integrableOn_residual_times_weight
    {S : Set ℝ} {alpha lambda₀ lambda₁ lambda₂ : ℝ} {w : ℝ → ℝ}
    (hg : IntegrableOn (fun x ↦ gAlpha alpha x * w x) S)
    (h0 : IntegrableOn (fun x ↦ x ^ 0 * w x) S)
    (h1 : IntegrableOn (fun x ↦ x ^ 1 * w x) S)
    (h2 : IntegrableOn (fun x ↦ x ^ 2 * w x) S) :
    IntegrableOn (fun x ↦ residual alpha lambda₀ lambda₁ lambda₂ x * w x) S := by
  have h := (((hg.sub (h0.const_mul lambda₀)).sub (h1.const_mul lambda₁)).sub
    (h2.const_mul lambda₂))
  apply h.congr_fun_ae
  filter_upwards with x
  simp only [Pi.sub_apply, residual]
  ring

lemma integrableOn_x_residual_times_weight
    {S : Set ℝ} {alpha lambda₀ lambda₁ lambda₂ : ℝ} {w : ℝ → ℝ}
    (hg : IntegrableOn (fun x ↦ x * gAlpha alpha x * w x) S)
    (h1 : IntegrableOn (fun x ↦ x ^ 1 * w x) S)
    (h2 : IntegrableOn (fun x ↦ x ^ 2 * w x) S)
    (h3 : IntegrableOn (fun x ↦ x ^ 3 * w x) S) :
    IntegrableOn
      (fun x ↦ x * residual alpha lambda₀ lambda₁ lambda₂ x * w x) S := by
  have h := (((hg.sub (h1.const_mul lambda₀)).sub (h2.const_mul lambda₁)).sub
    (h3.const_mul lambda₂))
  apply h.congr_fun_ae
  filter_upwards with x
  simp only [Pi.sub_apply, residual]
  ring

lemma setIntegral_residual_times_weight
    {S : Set ℝ} {alpha lambda₀ lambda₁ lambda₂ : ℝ} {w : ℝ → ℝ}
    (hg : IntegrableOn (fun x ↦ gAlpha alpha x * w x) S)
    (h0 : IntegrableOn (fun x ↦ x ^ 0 * w x) S)
    (h1 : IntegrableOn (fun x ↦ x ^ 1 * w x) S)
    (h2 : IntegrableOn (fun x ↦ x ^ 2 * w x) S) :
    (∫ x in S, residual alpha lambda₀ lambda₁ lambda₂ x * w x) =
      (∫ x in S, gAlpha alpha x * w x) -
        lambda₀ * (∫ x in S, x ^ 0 * w x) -
        lambda₁ * (∫ x in S, x ^ 1 * w x) -
        lambda₂ * (∫ x in S, x ^ 2 * w x) := by
  calc
    _ = ∫ x in S,
        ((((fun x ↦ gAlpha alpha x * w x) -
          fun x ↦ lambda₀ * (x ^ 0 * w x)) -
          fun x ↦ lambda₁ * (x ^ 1 * w x)) -
          fun x ↦ lambda₂ * (x ^ 2 * w x)) x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            simp only [Pi.sub_apply, residual]
            ring
    _ = _ := by
      simp only [Pi.sub_apply]
      calc
        (∫ x in S, gAlpha alpha x * w x - lambda₀ * (x ^ 0 * w x) -
            lambda₁ * (x ^ 1 * w x) - lambda₂ * (x ^ 2 * w x)) =
            (∫ x in S, gAlpha alpha x * w x - lambda₀ * (x ^ 0 * w x) -
              lambda₁ * (x ^ 1 * w x)) -
              ∫ x in S, lambda₂ * (x ^ 2 * w x) := by
                exact MeasureTheory.integral_sub
                  ((hg.sub (h0.const_mul lambda₀)).sub (h1.const_mul lambda₁))
                  (h2.const_mul lambda₂)
        _ = ((∫ x in S, gAlpha alpha x * w x - lambda₀ * (x ^ 0 * w x)) -
              ∫ x in S, lambda₁ * (x ^ 1 * w x)) -
              ∫ x in S, lambda₂ * (x ^ 2 * w x) := by
                congr 1
                exact MeasureTheory.integral_sub (hg.sub (h0.const_mul lambda₀))
                  (h1.const_mul lambda₁)
        _ = (((∫ x in S, gAlpha alpha x * w x) -
              ∫ x in S, lambda₀ * (x ^ 0 * w x)) -
              ∫ x in S, lambda₁ * (x ^ 1 * w x)) -
              ∫ x in S, lambda₂ * (x ^ 2 * w x) := by
                exact congrArg
                  (fun z : ℝ ↦ z - ∫ x in S, lambda₂ * (x ^ 2 * w x))
                  (congrArg
                    (fun z : ℝ ↦ z - ∫ x in S, lambda₁ * (x ^ 1 * w x))
                    (MeasureTheory.integral_sub hg (h0.const_mul lambda₀)))
        _ = _ := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul]

lemma setIntegral_x_residual_times_weight
    {S : Set ℝ} {alpha lambda₀ lambda₁ lambda₂ : ℝ} {w : ℝ → ℝ}
    (hg : IntegrableOn (fun x ↦ x * gAlpha alpha x * w x) S)
    (h1 : IntegrableOn (fun x ↦ x ^ 1 * w x) S)
    (h2 : IntegrableOn (fun x ↦ x ^ 2 * w x) S)
    (h3 : IntegrableOn (fun x ↦ x ^ 3 * w x) S) :
    (∫ x in S, x * residual alpha lambda₀ lambda₁ lambda₂ x * w x) =
      (∫ x in S, x * gAlpha alpha x * w x) -
        lambda₀ * (∫ x in S, x ^ 1 * w x) -
        lambda₁ * (∫ x in S, x ^ 2 * w x) -
        lambda₂ * (∫ x in S, x ^ 3 * w x) := by
  calc
    _ = ∫ x in S,
        ((((fun x ↦ x * gAlpha alpha x * w x) -
          fun x ↦ lambda₀ * (x ^ 1 * w x)) -
          fun x ↦ lambda₁ * (x ^ 2 * w x)) -
          fun x ↦ lambda₂ * (x ^ 3 * w x)) x := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards with x
            simp only [Pi.sub_apply, residual]
            ring
    _ = _ := by
      simp only [Pi.sub_apply]
      calc
        (∫ x in S, x * gAlpha alpha x * w x - lambda₀ * (x ^ 1 * w x) -
            lambda₁ * (x ^ 2 * w x) - lambda₂ * (x ^ 3 * w x)) =
            (∫ x in S, x * gAlpha alpha x * w x - lambda₀ * (x ^ 1 * w x) -
              lambda₁ * (x ^ 2 * w x)) -
              ∫ x in S, lambda₂ * (x ^ 3 * w x) := by
                exact MeasureTheory.integral_sub
                  ((hg.sub (h1.const_mul lambda₀)).sub (h2.const_mul lambda₁))
                  (h3.const_mul lambda₂)
        _ = ((∫ x in S, x * gAlpha alpha x * w x - lambda₀ * (x ^ 1 * w x)) -
              ∫ x in S, lambda₁ * (x ^ 2 * w x)) -
              ∫ x in S, lambda₂ * (x ^ 3 * w x) := by
                congr 1
                exact MeasureTheory.integral_sub (hg.sub (h1.const_mul lambda₀))
                  (h2.const_mul lambda₁)
        _ = (((∫ x in S, x * gAlpha alpha x * w x) -
              ∫ x in S, lambda₀ * (x ^ 1 * w x)) -
              ∫ x in S, lambda₁ * (x ^ 2 * w x)) -
              ∫ x in S, lambda₂ * (x ^ 3 * w x) := by
                exact congrArg
                  (fun z : ℝ ↦ z - ∫ x in S, lambda₂ * (x ^ 3 * w x))
                  (congrArg
                    (fun z : ℝ ↦ z - ∫ x in S, lambda₁ * (x ^ 2 * w x))
                    (MeasureTheory.integral_sub hg (h1.const_mul lambda₀)))
        _ = _ := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul]

/-! A genuine two-piece exponential on a right half-line cannot be a
constrained local extremum.  The two domination hypotheses are discharged
below from the negative tail slope for the concrete objective and moments. -/
theorem no_finiteLeft_genuine_kink_local_extremum_of_domination
    {alpha : ℝ} (halpha : 0 < alpha) {p : HalfLineParam}
    (hp : p ∈ finiteLeftKinkDomain) {r : ℝ}
    (hdomObj : HasRightTailDomination (gAlpha alpha) r p)
    (hdomMom : ∀ k : Fin 3,
      HasRightTailDomination (fun x ↦ x ^ k.val) r p)
    (hlocal : IsLocalExtrOn (halfLineIntegral (gAlpha alpha))
      ({u | halfLineMomentMap u = halfLineMomentMap p} ∩ finiteLeftKinkDomain) p) :
    False := by
  have hp' := hp
  change p 0 < p 4 ∧ 0 < p 3 ∧ p 2 - p 3 < 0 at hp
  rcases hp with ⟨hAm, hdelta, hslope⟩
  have hmax : IsLocalExtrOn (halfLineIntegral (gAlpha alpha))
      {u | halfLineMomentMap u = halfLineMomentMap p} p :=
    finiteLeft_localExtrOn_fiber_of_domain hp' hlocal
  have hpolyActual :=
    finiteLeft_moments_quadratic_nondegenerate_of_slope hAm hslope
  have hpoly : ∀ a b c : ℝ,
      a * halfLineLeftMoment p 0 + b * halfLineLeftMoment p 1 +
          c * halfLineLeftMoment p 2 = 0 →
      a * halfLineLeftMoment p 1 + b * halfLineLeftMoment p 2 +
          c * halfLineLeftMoment p 3 = 0 →
      a * halfLineRightMoment p 0 + b * halfLineRightMoment p 1 +
          c * halfLineRightMoment p 2 = 0 →
      a * halfLineRightMoment p 1 + b * halfLineRightMoment p 2 +
          c * halfLineRightMoment p 3 = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 := by
    simpa [finiteLeftActualLeftMoment, finiteLeftActualRightMoment,
      halfLineLeftMoment, halfLineRightMoment] using hpolyActual
  have hdelta0 : p 3 ≠ 0 := ne_of_gt hdelta
  have hrhoA : -exp (halfLineLeftExponent p (p 0)) ≠ 0 :=
    neg_ne_zero.mpr (exp_ne_zero _)
  obtain ⟨lambda₀, lambda₁, lambda₂,
      hL0, hL1, hR0, hR1, hA⟩ :=
    finiteLeft_KKT_residual_equations
      (M := halfLineMomentMap) (Phi := halfLineIntegral (gAlpha alpha))
      (theta := p)
      (L := halfLineLeftMoment p) (R := halfLineRightMoment p)
      (A := p 0) (m := p 4) (delta := p 3)
      (rhoA := -exp (halfLineLeftExponent p (p 0)))
      (HL0 := halfLineLeftIntegral (gAlpha alpha) p)
      (HL1 := halfLineLeftIntegral (fun x ↦ x * gAlpha alpha x) p)
      (HR0 := halfLineRightIntegral (gAlpha alpha) p)
      (HR1 := halfLineRightIntegral (fun x ↦ x * gAlpha alpha x) p)
      (hA := gAlpha alpha (p 0))
      hdelta0 hrhoA hpoly hmax
      (hasStrictFDerivAt_halfLineMomentMap hslope hdomMom)
      (hasStrictFDerivAt_halfLineIntegral (continuous_gAlpha alpha)
        hslope hdomObj)
  have hzL0 :
      (∫ x in p 0..p 4,
        residual alpha lambda₀ lambda₁ lambda₂ x * finiteLeftWeight p x) = 0 := by
    rw [intervalIntegral_residual_times_weight alpha lambda₀ lambda₁ lambda₂
      (p 0) (p 4) (continuous_finiteLeftWeight p)]
    change halfLineLeftIntegral (gAlpha alpha) p -
      lambda₀ * halfLineLeftMoment p 0 -
      lambda₁ * halfLineLeftMoment p 1 -
      lambda₂ * halfLineLeftMoment p 2 = 0
    linarith
  have hzL1 :
      (∫ x in p 0..p 4,
        x * residual alpha lambda₀ lambda₁ lambda₂ x * finiteLeftWeight p x) = 0 := by
    rw [intervalIntegral_x_residual_times_weight alpha lambda₀ lambda₁ lambda₂
      (p 0) (p 4) (continuous_finiteLeftWeight p)]
    change halfLineLeftIntegral (fun x ↦ x * gAlpha alpha x) p -
      lambda₀ * halfLineLeftMoment p 1 -
      lambda₁ * halfLineLeftMoment p 2 -
      lambda₂ * halfLineLeftMoment p 3 = 0
    linarith
  have htailMoment : ∀ n : ℕ,
      IntegrableOn (fun x ↦ x ^ n * finiteRightTailWeight p x) (Ioi (p 4)) :=
    fun n ↦ integrableOn_pow_mul_finiteRightTailWeight p n hslope (p 4)
  have htailG : IntegrableOn
      (fun x ↦ gAlpha alpha x * finiteRightTailWeight p x) (Ioi (p 4)) :=
    integrableOn_gAlpha_mul_finiteRightTailWeight halpha.le p hslope (p 4)
  have htailXG : IntegrableOn
      (fun x ↦ x * gAlpha alpha x * finiteRightTailWeight p x) (Ioi (p 4)) :=
    integrableOn_x_gAlpha_mul_finiteRightTailWeight halpha.le p hslope (p 4)
  have hzR0 :
      (∫ x in Ioi (p 4),
        residual alpha lambda₀ lambda₁ lambda₂ x * finiteRightTailWeight p x) = 0 := by
    rw [setIntegral_residual_times_weight htailG
      (htailMoment 0) (htailMoment 1) (htailMoment 2)]
    change halfLineRightIntegral (gAlpha alpha) p -
      lambda₀ * halfLineRightMoment p 0 -
      lambda₁ * halfLineRightMoment p 1 -
      lambda₂ * halfLineRightMoment p 2 = 0
    linarith
  have hzR1 :
      (∫ x in Ioi (p 4),
        x * residual alpha lambda₀ lambda₁ lambda₂ x *
          finiteRightTailWeight p x) = 0 := by
    rw [setIntegral_x_residual_times_weight htailXG
      (htailMoment 1) (htailMoment 2) (htailMoment 3)]
    change halfLineRightIntegral (fun x ↦ x * gAlpha alpha x) p -
      lambda₀ * halfLineRightMoment p 1 -
      lambda₁ * halfLineRightMoment p 2 -
      lambda₂ * halfLineRightMoment p 3 = 0
    linarith
  have hrL : IntegrableOn
      (fun x ↦ residual alpha lambda₀ lambda₁ lambda₂ x *
        finiteLeftWeight p x) (Ioo (p 0) (p 4)) :=
    ((continuous_residual alpha lambda₀ lambda₁ lambda₂).mul
      (continuous_finiteLeftWeight p)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hxrL : IntegrableOn
      (fun x ↦ x * residual alpha lambda₀ lambda₁ lambda₂ x *
        finiteLeftWeight p x) (Ioo (p 0) (p 4)) :=
    ((continuous_id.mul
      (continuous_residual alpha lambda₀ lambda₁ lambda₂)).mul
      (continuous_finiteLeftWeight p)).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hrR : IntegrableOn
      (fun x ↦ residual alpha lambda₀ lambda₁ lambda₂ x *
        finiteRightTailWeight p x) (Ioi (p 4)) :=
    integrableOn_residual_times_weight htailG
      (htailMoment 0) (htailMoment 1) (htailMoment 2)
  have hxrR : IntegrableOn
      (fun x ↦ x * residual alpha lambda₀ lambda₁ lambda₂ x *
        finiteRightTailWeight p x) (Ioi (p 4)) :=
    integrableOn_x_residual_times_weight htailXG
      (htailMoment 1) (htailMoment 2) (htailMoment 3)
  have hL0set :
      (∫ x in Ioo (p 0) (p 4),
        residual alpha lambda₀ lambda₁ lambda₂ x * finiteLeftWeight p x) = 0 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hAm.le]
    exact hzL0
  have hL1set :
      (∫ x in Ioo (p 0) (p 4),
        x * residual alpha lambda₀ lambda₁ lambda₂ x *
          finiteLeftWeight p x) = 0 := by
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hAm.le]
    exact hzL1
  have hend : residual alpha lambda₀ lambda₁ lambda₂ (p 0) = 0 := by
    unfold residual
    linarith
  exact finite_left_endpoint_contradiction halpha hAm
    (continuous_finiteLeftWeight p).continuousOn
    (continuous_finiteRightTailWeight p).continuousOn
    (fun x hx ↦ exp_pos _) (fun x hx ↦ exp_pos _)
    hrL hxrL hrR hxrR hL0set hL1set hzR0 hzR1 hend

theorem no_finiteLeft_genuine_kink_local_extremum
    {alpha : ℝ} (halpha : 0 < alpha) {p : HalfLineParam}
    (hp : p ∈ finiteLeftKinkDomain)
    (hlocal : IsLocalExtrOn (halfLineIntegral (gAlpha alpha))
      ({u | halfLineMomentMap u = halfLineMomentMap p} ∩ finiteLeftKinkDomain) p) :
    False := by
  have hslope : p 2 - p 3 < 0 := hp.2.2
  exact no_finiteLeft_genuine_kink_local_extremum_of_domination halpha hp
    (hasRightTailDomination_gAlpha halpha.le p hslope)
    (fun k ↦ hasRightTailDomination_pow k.val p hslope) hlocal

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/HalfLineReflectionCore.lean` -/



open Set

namespace LogConcaveClaimI

/-- Reflection of the parameters `(endpoint,c,beta,delta,kink)`.  The same
formula is its own inverse. -/
def halfLineReflect (p : HalfLineParam) : HalfLineParam :=
  ![-p 0, p 1 + p 3 * p 4, p 3 - p 2, p 3, -p 4]

@[simp] lemma halfLineReflect_zero (p : HalfLineParam) :
    halfLineReflect p 0 = -p 0 := by simp [halfLineReflect]

@[simp] lemma halfLineReflect_one (p : HalfLineParam) :
    halfLineReflect p 1 = p 1 + p 3 * p 4 := by simp [halfLineReflect]

@[simp] lemma halfLineReflect_two (p : HalfLineParam) :
    halfLineReflect p 2 = p 3 - p 2 := by simp [halfLineReflect]

@[simp] lemma halfLineReflect_three (p : HalfLineParam) :
    halfLineReflect p 3 = p 3 := by simp [halfLineReflect]

@[simp] lemma halfLineReflect_four (p : HalfLineParam) :
    halfLineReflect p 4 = -p 4 := by simp [halfLineReflect]

@[simp] theorem halfLineReflect_involutive (p : HalfLineParam) :
    halfLineReflect (halfLineReflect p) = p := by
  funext i
  fin_cases i <;> simp [halfLineReflect] <;> ring

lemma continuous_halfLineReflect : Continuous halfLineReflect := by
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;> simp [halfLineReflect] <;> fun_prop

/-- Domain for a genuine kink on a left half-line.  Coordinate `0` is the
finite right endpoint and coordinate `4` the kink. -/
def finiteRightKinkDomain : Set HalfLineParam :=
  {p | p 4 < p 0 ∧ 0 < p 3 ∧ 0 < p 2}

theorem halfLineReflect_mem_finiteLeft_iff (p : HalfLineParam) :
    halfLineReflect p ∈ finiteLeftKinkDomain ↔ p ∈ finiteRightKinkDomain := by
  simp only [finiteLeftKinkDomain, finiteRightKinkDomain, Set.mem_setOf_eq,
    halfLineReflect_zero, halfLineReflect_two, halfLineReflect_three,
    halfLineReflect_four]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> constructor
  · linarith
  · exact ⟨h2, by linarith⟩
  · linarith
  · exact ⟨h2, by linarith⟩

theorem halfLineReflect_mem_finiteRight_iff (p : HalfLineParam) :
    halfLineReflect p ∈ finiteRightKinkDomain ↔ p ∈ finiteLeftKinkDomain := by
  rw [← halfLineReflect_mem_finiteLeft_iff (halfLineReflect p)]
  simp

def finiteRightObjective (alpha : ℝ) (p : HalfLineParam) : ℝ :=
  halfLineIntegral (gAlpha alpha) (halfLineReflect p)

def finiteRightMomentMap (p : HalfLineParam) (k : Fin 3) : ℝ :=
  (-1 : ℝ) ^ k.val * halfLineMomentMap (halfLineReflect p) k

theorem finiteRightMomentMap_eq_iff (p q : HalfLineParam) :
    finiteRightMomentMap p = finiteRightMomentMap q ↔
      halfLineMomentMap (halfLineReflect p) =
        halfLineMomentMap (halfLineReflect q) := by
  constructor
  · intro h
    funext k
    have hk := congrFun h k
    fin_cases k <;> norm_num [finiteRightMomentMap] at hk ⊢ <;> linarith
  · intro h
    funext k
    rw [finiteRightMomentMap, finiteRightMomentMap, congrFun h k]

/-- Local extremality transports across parameter reflection. -/
theorem finiteRight_localExtr_reflect
    {alpha : ℝ} {p : HalfLineParam}
    (hp : p ∈ finiteRightKinkDomain)
    (hlocal : IsLocalExtrOn (finiteRightObjective alpha)
      ({u | finiteRightMomentMap u = finiteRightMomentMap p} ∩
        finiteRightKinkDomain) p) :
    IsLocalExtrOn (halfLineIntegral (gAlpha alpha))
      ({u | halfLineMomentMap u = halfLineMomentMap (halfLineReflect p)} ∩
        finiteLeftKinkDomain) (halfLineReflect p) := by
  let S := {u | halfLineMomentMap u = halfLineMomentMap (halfLineReflect p)} ∩
    finiteLeftKinkDomain
  let T := {u | finiteRightMomentMap u = finiteRightMomentMap p} ∩
    finiteRightKinkDomain
  have hlocal' : IsLocalExtrOn (finiteRightObjective alpha) T
      (halfLineReflect (halfLineReflect p)) := by
    simpa only [halfLineReflect_involutive] using hlocal
  have hcomp := hlocal'.comp_continuousOn halfLineReflect
    (s := S) (t := T) (b := halfLineReflect p)
  have hsubset : S ⊆ halfLineReflect ⁻¹' T := by
    intro u hu
    rcases hu with ⟨hmom, hdom⟩
    constructor
    · apply (finiteRightMomentMap_eq_iff (halfLineReflect u) p).2
      simpa using hmom
    · exact (halfLineReflect_mem_finiteRight_iff u).2 hdom
  have hcont : ContinuousOn halfLineReflect S :=
    continuous_halfLineReflect.continuousOn
  have hb : halfLineReflect p ∈ S := by
    constructor
    · rfl
    · exact (halfLineReflect_mem_finiteLeft_iff p).2 hp
  have h := hcomp hsubset hcont hb
  simpa [S, T, finiteRightObjective, Function.comp_def] using h

end LogConcaveClaimI

/-! ## Flattened source: `lean_i/FiniteRightClaimI.lean` -/



open Real Set MeasureTheory intervalIntegral
open scoped Interval

namespace LogConcaveClaimI

/-!
# The finite-right half-line, by literal reflection

The coordinates are `(B,c,beta,delta,m)`.  The density is proportional to
`exp (c+beta*x)` on `(-infinity,m]` and to
`exp (c+beta*x-delta*(x-m))` on `[m,B]`.
-/

def finiteRightLeftExponent (p : HalfLineParam) (x : ℝ) : ℝ :=
  p 1 + p 2 * x

def finiteRightRightExponent (p : HalfLineParam) (x : ℝ) : ℝ :=
  p 1 + p 2 * x - p 3 * (x - p 4)

def finiteRightLeftIntegrand (q : ℝ → ℝ) (p : HalfLineParam) (x : ℝ) : ℝ :=
  q x * exp (finiteRightLeftExponent p x)

def finiteRightRightIntegrand (q : ℝ → ℝ) (p : HalfLineParam) (x : ℝ) : ℝ :=
  q x * exp (finiteRightRightExponent p x)

def finiteRightLeftTailIntegral (q : ℝ → ℝ) (p : HalfLineParam) : ℝ :=
  ∫ x in Iic (p 4), finiteRightLeftIntegrand q p x

def finiteRightRightCompactIntegral (q : ℝ → ℝ) (p : HalfLineParam) : ℝ :=
  ∫ x in p 4..p 0, finiteRightRightIntegrand q p x

def finiteRightActualIntegral (q : ℝ → ℝ) (p : HalfLineParam) : ℝ :=
  finiteRightLeftTailIntegral q p + finiteRightRightCompactIntegral q p

lemma halfLineLeftIntegrand_reflect
    (q : ℝ → ℝ) (p : HalfLineParam) (y : ℝ) :
    halfLineLeftIntegrand (fun x ↦ q (-x)) (halfLineReflect p) y =
      finiteRightRightIntegrand q p (-y) := by
  simp only [halfLineLeftIntegrand, finiteRightRightIntegrand,
    halfLineLeftExponent, finiteRightRightExponent,
    halfLineReflect_one, halfLineReflect_two, halfLineReflect_three,
    halfLineReflect_four]
  congr 2
  ring

lemma halfLineRightIntegrand_reflect
    (q : ℝ → ℝ) (p : HalfLineParam) (y : ℝ) :
    halfLineRightIntegrand (fun x ↦ q (-x)) (halfLineReflect p) y =
      finiteRightLeftIntegrand q p (-y) := by
  simp only [halfLineRightIntegrand, finiteRightLeftIntegrand,
    halfLineRightExponent, finiteRightLeftExponent,
    halfLineReflect_one, halfLineReflect_two, halfLineReflect_three,
    halfLineReflect_four]
  congr 2
  ring

/-- Literal change of variables on the compact piece. -/
theorem halfLineLeftIntegral_reflect
    (q : ℝ → ℝ) (p : HalfLineParam) :
    halfLineLeftIntegral (fun x ↦ q (-x)) (halfLineReflect p) =
      finiteRightRightCompactIntegral q p := by
  unfold halfLineLeftIntegral finiteRightRightCompactIntegral
  simp only [halfLineReflect_zero, halfLineReflect_four]
  calc
    (∫ y in -p 0..-p 4,
      halfLineLeftIntegrand (fun x ↦ q (-x)) (halfLineReflect p) y) =
        ∫ y in -p 0..-p 4, finiteRightRightIntegrand q p (-y) := by
          apply intervalIntegral.integral_congr
          intro y hy
          exact halfLineLeftIntegrand_reflect q p y
    _ = ∫ x in p 4..p 0, finiteRightRightIntegrand q p x := by
      simpa using (intervalIntegral.integral_comp_neg
        (f := finiteRightRightIntegrand q p)
        (a := -p 0) (b := -p 4))

/-- Literal change of variables on the improper piece. -/
theorem halfLineRightIntegral_reflect
    (q : ℝ → ℝ) (p : HalfLineParam) :
    halfLineRightIntegral (fun x ↦ q (-x)) (halfLineReflect p) =
      finiteRightLeftTailIntegral q p := by
  unfold halfLineRightIntegral finiteRightLeftTailIntegral
  simp only [halfLineReflect_four]
  calc
    (∫ y in Ioi (-p 4),
      halfLineRightIntegrand (fun x ↦ q (-x)) (halfLineReflect p) y) =
        ∫ y in Ioi (-p 4), finiteRightLeftIntegrand q p (-y) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with y
          exact halfLineRightIntegrand_reflect q p y
    _ = ∫ x in Iic (p 4), finiteRightLeftIntegrand q p x := by
      simpa only [neg_neg] using
        (integral_comp_neg_Ioi (-p 4) (finiteRightLeftIntegrand q p))

/-- The literal finite-right integral is exactly the reflected finite-left
integral.  No integrability assumption is needed for this identity. -/
theorem finiteRightActualIntegral_eq_reflect
    (q : ℝ → ℝ) (p : HalfLineParam) :
    finiteRightActualIntegral q p =
      halfLineIntegral (fun x ↦ q (-x)) (halfLineReflect p) := by
  rw [finiteRightActualIntegral, halfLineIntegral,
    halfLineLeftIntegral_reflect, halfLineRightIntegral_reflect]
  ring

lemma halfLineIntegral_const_mul (a : ℝ) (q : ℝ → ℝ)
    (p : HalfLineParam) :
    halfLineIntegral (fun x ↦ a * q x) p = a * halfLineIntegral q p := by
  have hL : halfLineLeftIntegral (fun x ↦ a * q x) p =
      a * halfLineLeftIntegral q p := by
    unfold halfLineLeftIntegral halfLineLeftIntegrand
    calc
      (∫ x in p 0..p 4, (a * q x) * exp (halfLineLeftExponent p x)) =
          ∫ x in p 0..p 4, a * (q x * exp (halfLineLeftExponent p x)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have hR : halfLineRightIntegral (fun x ↦ a * q x) p =
      a * halfLineRightIntegral q p := by
    unfold halfLineRightIntegral halfLineRightIntegrand
    calc
      (∫ x in Ioi (p 4), (a * q x) * exp (halfLineRightExponent p x)) =
          ∫ x in Ioi (p 4), a * (q x * exp (halfLineRightExponent p x)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with x
            ring
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  unfold halfLineIntegral
  rw [hL, hR]
  ring

def finiteRightActualMomentMap (p : HalfLineParam) (k : Fin 3) : ℝ :=
  finiteRightActualIntegral (fun x ↦ x ^ k.val) p

/-- Odd moments change sign under reflection; even moments do not. -/
theorem finiteRightActualMomentMap_eq (p : HalfLineParam) :
    finiteRightActualMomentMap p = finiteRightMomentMap p := by
  funext k
  rw [finiteRightActualMomentMap, finiteRightActualIntegral_eq_reflect]
  have hfun : (fun x : ℝ ↦ (-x) ^ k.val) =
      (fun x ↦ (-1 : ℝ) ^ k.val * x ^ k.val) := by
    funext x
    rw [neg_pow]
  rw [hfun, halfLineIntegral_const_mul]
  rfl

lemma gAlpha_neg (alpha x : ℝ) : gAlpha alpha (-x) = gAlpha alpha x := by
  simp [gAlpha]

/-- The objective is invariant under reflection. -/
theorem finiteRightActualObjective_eq (alpha : ℝ) :
    finiteRightActualIntegral (gAlpha alpha) = finiteRightObjective alpha := by
  funext p
  rw [finiteRightActualIntegral_eq_reflect]
  congr 1
  funext x
  exact gAlpha_neg alpha x

/-- A genuine two-piece exponential on a left half-line cannot be a
constrained local extremum. -/
theorem no_finiteRight_genuine_kink_local_extremum
    {alpha : ℝ} (halpha : 0 < alpha) {p : HalfLineParam}
    (hp : p ∈ finiteRightKinkDomain)
    (hlocal : IsLocalExtrOn (finiteRightActualIntegral (gAlpha alpha))
      ({u | finiteRightActualMomentMap u = finiteRightActualMomentMap p} ∩
        finiteRightKinkDomain) p) :
    False := by
  have hObj := finiteRightActualObjective_eq alpha
  have hMom : finiteRightActualMomentMap = finiteRightMomentMap := by
    funext u
    exact finiteRightActualMomentMap_eq u
  rw [hObj, hMom] at hlocal
  have href := finiteRight_localExtr_reflect hp hlocal
  exact no_finiteLeft_genuine_kink_local_extremum halpha
    ((halfLineReflect_mem_finiteLeft_iff p).2 hp) href

end LogConcaveClaimI

/-! ## Flattened source: `lean_core/CompactSplitIntegral.lean` -/


/-!
# The compact split-exponential variation

This file differentiates the finite-dimensional variation used in the compact
one-piece case.  The hinge is split at its fixed point `s`, so neither the
absolute value nor `max` occurs in the differentiation argument.
-/

open Filter Set MeasureTheory
open scoped Topology Interval

namespace LogConcaveExtremum.CompactSplitIntegral

open ParametricInterval


abbrev Free := ℝ × ℝ
abbrev Corr := Fin 3 → ℝ
abbrev Param := Free × Corr

/-- `HasStrictFDerivAt` with the norm-induced structures selected explicitly.
The explicit selection avoids the harmless product-instance diamond between
the algebraic and norm-induced structures. -/
abbrev HasStrictParamFDerivAt
    (f : Param → ℝ) (f' : Param →L[ℝ] ℝ) (p : Param) : Prop :=
  @HasStrictFDerivAt ℝ DenselyNormedField.toNontriviallyNormedField Param
    Prod.normedAddCommGroup.toAddCommGroup
    Prod.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    ℝ Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    f f' p

/-- The correction coordinates are, in order, normalization, left endpoint,
and right endpoint. -/
def corrTriple (c A B : ℝ) : Corr :=
  fun i ↦ if i = 0 then c else if i = 1 then A else B

def baseParam (c A B : ℝ) : Param := ((0, 0), corrTriple c A B)

def betaCLM : Param →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ) ∘L
    (ContinuousLinearMap.fst ℝ Free Corr)

def etaCLM : Param →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ) ∘L
    (ContinuousLinearMap.fst ℝ Free Corr)

def corrCLM (i : Fin 3) : Param →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i) ∘L (ContinuousLinearMap.snd ℝ Free Corr)

def leftScore (x : ℝ) : Param →L[ℝ] ℝ :=
  corrCLM 0 + x • betaCLM

def rightScore (s x : ℝ) : Param →L[ℝ] ℝ :=
  leftScore x - (x - s) • etaCLM

def leftIntegrand (q : ℝ → ℝ) (beta : ℝ) (p : Param) (x : ℝ) : ℝ :=
  q x * Real.exp (beta * x + leftScore x p)

def rightIntegrand (q : ℝ → ℝ) (beta s : ℝ) (p : Param) (x : ℝ) : ℝ :=
  q x * Real.exp (beta * x + rightScore s x p)

def leftIntegrandFDeriv (q : ℝ → ℝ) (beta : ℝ) (p : Param) (x : ℝ) :
    Param →L[ℝ] ℝ :=
  (q x * Real.exp (beta * x + leftScore x p)) • leftScore x

def rightIntegrandFDeriv (q : ℝ → ℝ) (beta s : ℝ) (p : Param) (x : ℝ) :
    Param →L[ℝ] ℝ :=
  (q x * Real.exp (beta * x + rightScore s x p)) • rightScore s x

lemma corrTriple_zero (c A B : ℝ) : corrTriple c A B 0 = c := by
  simp [corrTriple]

lemma corrTriple_one (c A B : ℝ) : corrTriple c A B 1 = A := by
  simp [corrTriple]

lemma corrTriple_two (c A B : ℝ) : corrTriple c A B 2 = B := by
  simp [corrTriple]

@[simp] lemma betaCLM_base (c A B : ℝ) : betaCLM (baseParam c A B) = 0 := by
  rfl

@[simp] lemma etaCLM_base (c A B : ℝ) : etaCLM (baseParam c A B) = 0 := by
  rfl

@[simp] lemma corrCLM_base_zero (c A B : ℝ) :
    corrCLM 0 (baseParam c A B) = c := by
  simp [corrCLM, baseParam, corrTriple]

@[simp] lemma corrCLM_base_one (c A B : ℝ) :
    corrCLM 1 (baseParam c A B) = A := by
  simp [corrCLM, baseParam, corrTriple]

@[simp] lemma corrCLM_base_two (c A B : ℝ) :
    corrCLM 2 (baseParam c A B) = B := by
  simp [corrCLM, baseParam, corrTriple]

@[simp] lemma leftScore_base (c A B x : ℝ) :
    leftScore x (baseParam c A B) = c := by
  simp [leftScore]

@[simp] lemma rightScore_base (c A B s x : ℝ) :
    rightScore s x (baseParam c A B) = c := by
  simp [rightScore]

@[simp] lemma leftIntegrand_base
    (q : ℝ → ℝ) (c beta A B x : ℝ) :
    leftIntegrand q beta (baseParam c A B) x =
      q x * Real.exp (c + beta * x) := by
  simp [leftIntegrand, add_comm]

@[simp] lemma rightIntegrand_base
    (q : ℝ → ℝ) (c beta A B s x : ℝ) :
    rightIntegrand q beta s (baseParam c A B) x =
      q x * Real.exp (c + beta * x) := by
  simp [rightIntegrand, add_comm]

@[simp] lemma leftIntegrandFDeriv_base
    (q : ℝ → ℝ) (c beta A B x : ℝ) :
    leftIntegrandFDeriv q beta (baseParam c A B) x =
      (q x * Real.exp (c + beta * x)) • leftScore x := by
  simp [leftIntegrandFDeriv, add_comm]

@[simp] lemma rightIntegrandFDeriv_base
    (q : ℝ → ℝ) (c beta A B s x : ℝ) :
    rightIntegrandFDeriv q beta s (baseParam c A B) x =
      (q x * Real.exp (c + beta * x)) • rightScore s x := by
  simp [rightIntegrandFDeriv, add_comm]

lemma hasFDerivAt_leftIntegrand
    (q : ℝ → ℝ) (beta x : ℝ) (p : Param) :
    HasFDerivAt (fun y ↦ leftIntegrand q beta y x)
      (leftIntegrandFDeriv q beta p x) p := by
  have harg : HasFDerivAt (fun y ↦ beta * x + leftScore x y) (leftScore x) p :=
    (leftScore x).hasFDerivAt.const_add (beta * x)
  have h := harg.exp.const_mul (q x)
  simpa only [leftIntegrand, leftIntegrandFDeriv, smul_smul] using h

lemma hasFDerivAt_rightIntegrand
    (q : ℝ → ℝ) (beta s x : ℝ) (p : Param) :
    HasFDerivAt (fun y ↦ rightIntegrand q beta s y x)
      (rightIntegrandFDeriv q beta s p x) p := by
  have harg : HasFDerivAt (fun y ↦ beta * x + rightScore s x y) (rightScore s x) p :=
    (rightScore s x).hasFDerivAt.const_add (beta * x)
  have h := harg.exp.const_mul (q x)
  simpa only [rightIntegrand, rightIntegrandFDeriv, smul_smul] using h

lemma continuous_uncurry_leftIntegrand
    (q : ℝ → ℝ) (hq : Continuous q) (beta : ℝ) :
    Continuous (Function.uncurry (leftIntegrand q beta)) := by
  unfold leftIntegrand leftScore corrCLM betaCLM
  fun_prop

lemma continuous_uncurry_rightIntegrand
    (q : ℝ → ℝ) (hq : Continuous q) (beta s : ℝ) :
    Continuous (Function.uncurry (rightIntegrand q beta s)) := by
  unfold rightIntegrand rightScore leftScore corrCLM betaCLM etaCLM
  fun_prop

lemma continuous_uncurry_leftIntegrandFDeriv
    (q : ℝ → ℝ) (hq : Continuous q) (beta : ℝ) :
    Continuous (Function.uncurry (leftIntegrandFDeriv q beta)) := by
  unfold leftIntegrandFDeriv leftScore corrCLM betaCLM
  fun_prop

lemma continuous_uncurry_rightIntegrandFDeriv
    (q : ℝ → ℝ) (hq : Continuous q) (beta s : ℝ) :
    Continuous (Function.uncurry (rightIntegrandFDeriv q beta s)) := by
  unfold rightIntegrandFDeriv rightScore leftScore corrCLM betaCLM etaCLM
  fun_prop

/-- The split variation before imposing the three moment constraints. -/
def splitIntegral (q : ℝ → ℝ) (beta s : ℝ) (p : Param) : ℝ :=
  (∫ x in corrCLM 1 p..s, leftIntegrand q beta p x) +
    ∫ x in s..corrCLM 2 p, rightIntegrand q beta s p x

/-- At the unperturbed parameter the split integral is the original integral,
independently of the splitting point. -/
theorem splitIntegral_base
    (q : ℝ → ℝ) (hq : Continuous q) (c beta A B s : ℝ) :
    splitIntegral q beta s (baseParam c A B) =
      ∫ x in A..B, q x * Real.exp (c + beta * x) := by
  unfold splitIntegral
  simp only [corrCLM_base_one, corrCLM_base_two,
    leftIntegrand_base, rightIntegrand_base]
  have hc : Continuous (fun x ↦ q x * Real.exp (c + beta * x)) := by
    fun_prop
  exact intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable A s) (hc.intervalIntegrable s B)

/-- The transparent, expanded form of the derivative. -/
def splitIntegralFDerivExplicit
    (q : ℝ → ℝ) (c beta A B s : ℝ) : Param →L[ℝ] ℝ :=
  (∫ x in A..s, (q x * Real.exp (c + beta * x)) • leftScore x) +
  (∫ x in s..B, (q x * Real.exp (c + beta * x)) • rightScore s x) -
  (q A * Real.exp (c + beta * A)) • corrCLM 1 +
  (q B * Real.exp (c + beta * B)) • corrCLM 2

/-- The derivative delivered directly by the moving-endpoint Leibniz rule for
the left half of the split integral. -/
def leftIntegralFDeriv
    (q : ℝ → ℝ) (c beta A B s : ℝ) : Param →L[ℝ] ℝ :=
  (((∫ x in A..s, leftIntegrandFDeriv q beta (baseParam c A B) x).coprod
      (endpointFDeriv (leftIntegrand q beta) (baseParam c A B) A s)) ∘L
    ((ContinuousLinearMap.id ℝ Param).prod ((corrCLM 1).prod 0)))

/-- The derivative delivered directly by the moving-endpoint Leibniz rule for
the right half of the split integral. -/
def rightIntegralFDeriv
    (q : ℝ → ℝ) (c beta A B s : ℝ) : Param →L[ℝ] ℝ :=
  (((∫ x in s..B, rightIntegrandFDeriv q beta s (baseParam c A B) x).coprod
      (endpointFDeriv (rightIntegrand q beta s) (baseParam c A B) s B)) ∘L
    ((ContinuousLinearMap.id ℝ Param).prod ((0 : Param →L[ℝ] ℝ).prod (corrCLM 2))))

/-- The derivative of the whole split variation. -/
def splitIntegralFDeriv
    (q : ℝ → ℝ) (c beta A B s : ℝ) : Param →L[ℝ] ℝ :=
  leftIntegralFDeriv q c beta A B s + rightIntegralFDeriv q c beta A B s

/-- Strict differentiation of the split variation.  This is the analytic
input needed by the finite-dimensional KKT argument. -/
theorem hasStrictFDerivAt_splitIntegral
    (q : ℝ → ℝ) (hq : Continuous q) (c beta A B s : ℝ) :
    HasStrictParamFDerivAt (splitIntegral q beta s)
      (splitIntegralFDeriv q c beta A B s) (baseParam c A B) := by
  have hleft := hasStrictFDerivAt_movingIntervalIntegral_of_continuous
    (F := leftIntegrand q beta)
    (F' := leftIntegrandFDeriv q beta)
    (A := fun p ↦ corrCLM 1 p) (B := fun _ : Param ↦ s)
    (p₀ := baseParam c A B) (A' := corrCLM 1) (B' := 0)
    (continuous_uncurry_leftIntegrand q hq beta)
    (continuous_uncurry_leftIntegrandFDeriv q hq beta)
    (fun p x ↦ hasFDerivAt_leftIntegrand q beta x p)
    (corrCLM 1).hasStrictFDerivAt (hasStrictFDerivAt_const s (baseParam c A B))
  have hright := hasStrictFDerivAt_movingIntervalIntegral_of_continuous
    (F := rightIntegrand q beta s)
    (F' := rightIntegrandFDeriv q beta s)
    (A := fun _ : Param ↦ s) (B := fun p ↦ corrCLM 2 p)
    (p₀ := baseParam c A B) (A' := 0) (B' := corrCLM 2)
    (continuous_uncurry_rightIntegrand q hq beta s)
    (continuous_uncurry_rightIntegrandFDeriv q hq beta s)
    (fun p x ↦ hasFDerivAt_rightIntegrand q beta s x p)
    (hasStrictFDerivAt_const s (baseParam c A B)) (corrCLM 2).hasStrictFDerivAt
  unfold splitIntegralFDeriv leftIntegralFDeriv rightIntegralFDeriv
  convert hleft.add hright using 1
  · funext p
    rfl
  · rw [corrCLM_base_one, corrCLM_base_two]

/-- The derivative produced by Leibniz' rule is the transparent formula with
two parameter-integral terms and the two endpoint terms. -/
theorem splitIntegralFDeriv_eq_explicit
    (q : ℝ → ℝ) (hq : Continuous q) (c beta A B s : ℝ) :
    splitIntegralFDeriv q c beta A B s =
      splitIntegralFDerivExplicit q c beta A B s := by
  have hL : IntervalIntegrable
      (fun x ↦ (q x * Real.exp (c + beta * x)) • leftScore x)
      MeasureTheory.volume A s := by
    have hc : Continuous
        (fun x ↦ (q x * Real.exp (c + beta * x)) • leftScore x) := by
      unfold leftScore corrCLM betaCLM
      fun_prop
    exact hc.intervalIntegrable A s
  have hR : IntervalIntegrable
      (fun x ↦ (q x * Real.exp (c + beta * x)) • rightScore s x)
      MeasureTheory.volume s B := by
    have hc : Continuous
        (fun x ↦ (q x * Real.exp (c + beta * x)) • rightScore s x) := by
      unfold rightScore leftScore corrCLM betaCLM etaCLM
      fun_prop
    exact hc.intervalIntegrable s B
  apply ContinuousLinearMap.ext
  intro v
  unfold splitIntegralFDeriv leftIntegralFDeriv rightIntegralFDeriv
    splitIntegralFDerivExplicit
  simp only [leftIntegrandFDeriv_base, rightIntegrandFDeriv_base,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.intervalIntegral_apply hL v,
    ContinuousLinearMap.intervalIntegral_apply hR v,
    endpointFDeriv, leftIntegrand_base, rightIntegrand_base]
  simp [ContinuousLinearMap.smulRight_apply]
  ring

/-- Pointwise form of the derivative. -/
theorem splitIntegralFDeriv_apply
    (q : ℝ → ℝ) (hq : Continuous q) (c beta A B s : ℝ) (v : Param) :
    splitIntegralFDeriv q c beta A B s v =
      (∫ x in A..s,
        q x * Real.exp (c + beta * x) * leftScore x v) +
      (∫ x in s..B,
        q x * Real.exp (c + beta * x) * rightScore s x v) -
      q A * Real.exp (c + beta * A) * corrCLM 1 v +
      q B * Real.exp (c + beta * B) * corrCLM 2 v := by
  have hL : IntervalIntegrable
      (fun x ↦ (q x * Real.exp (c + beta * x)) • leftScore x)
      MeasureTheory.volume A s := by
    have hc : Continuous
        (fun x ↦ (q x * Real.exp (c + beta * x)) • leftScore x) := by
      unfold leftScore corrCLM betaCLM
      fun_prop
    exact hc.intervalIntegrable A s
  have hR : IntervalIntegrable
      (fun x ↦ (q x * Real.exp (c + beta * x)) • rightScore s x)
      MeasureTheory.volume s B := by
    have hc : Continuous
        (fun x ↦ (q x * Real.exp (c + beta * x)) • rightScore s x) := by
      unfold rightScore leftScore corrCLM betaCLM etaCLM
      fun_prop
    exact hc.intervalIntegrable s B
  rw [splitIntegralFDeriv_eq_explicit q hq]
  unfold splitIntegralFDerivExplicit
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.intervalIntegral_apply hL v,
    ContinuousLinearMap.intervalIntegral_apply hR v,
    ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Unit direction in the normalization correction `c`. -/
def cDirection : Param := ((0, 0), corrTriple 1 0 0)

/-- Unit direction in the free log-slope increment. -/
def betaDirection : Param := ((1, 0), corrTriple 0 0 0)

/-- Unit direction in the one-sided hinge parameter. -/
def etaDirection : Param := ((0, 1), corrTriple 0 0 0)

/-- Unit direction in the left endpoint. -/
def leftEndpointDirection : Param := ((0, 0), corrTriple 0 1 0)

/-- Unit direction in the right endpoint. -/
def rightEndpointDirection : Param := ((0, 0), corrTriple 0 0 1)

@[simp] lemma leftScore_cDirection (x : ℝ) : leftScore x cDirection = 1 := by
  simp [leftScore, cDirection, corrCLM, betaCLM, corrTriple]

@[simp] lemma etaCLM_cDirection : etaCLM cDirection = 0 := by rfl

@[simp] lemma rightScore_cDirection (s x : ℝ) : rightScore s x cDirection = 1 := by
  simp [rightScore]

@[simp] lemma leftScore_betaDirection (x : ℝ) : leftScore x betaDirection = x := by
  simp [leftScore, betaDirection, corrCLM, betaCLM, corrTriple]

@[simp] lemma etaCLM_betaDirection : etaCLM betaDirection = 0 := by rfl

@[simp] lemma rightScore_betaDirection (s x : ℝ) : rightScore s x betaDirection = x := by
  simp [rightScore]

@[simp] lemma leftScore_etaDirection (x : ℝ) : leftScore x etaDirection = 0 := by
  simp [leftScore, etaDirection, corrCLM, betaCLM, corrTriple]

@[simp] lemma etaCLM_etaDirection : etaCLM etaDirection = 1 := by rfl

@[simp] lemma rightScore_etaDirection (s x : ℝ) :
    rightScore s x etaDirection = -(x - s) := by
  unfold rightScore
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    leftScore_etaDirection, etaCLM_etaDirection]
  simp

@[simp] lemma leftScore_leftEndpointDirection (x : ℝ) :
    leftScore x leftEndpointDirection = 0 := by
  simp [leftScore, leftEndpointDirection, corrCLM, betaCLM, corrTriple]

@[simp] lemma etaCLM_leftEndpointDirection : etaCLM leftEndpointDirection = 0 := by rfl

@[simp] lemma rightScore_leftEndpointDirection (s x : ℝ) :
    rightScore s x leftEndpointDirection = 0 := by
  unfold rightScore
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    leftScore_leftEndpointDirection, etaCLM_leftEndpointDirection]
  simp

@[simp] lemma leftScore_rightEndpointDirection (x : ℝ) :
    leftScore x rightEndpointDirection = 0 := by
  simp [leftScore, rightEndpointDirection, corrCLM, betaCLM, corrTriple]

@[simp] lemma etaCLM_rightEndpointDirection : etaCLM rightEndpointDirection = 0 := by rfl

@[simp] lemma rightScore_rightEndpointDirection (s x : ℝ) :
    rightScore s x rightEndpointDirection = 0 := by
  unfold rightScore
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    leftScore_rightEndpointDirection, etaCLM_rightEndpointDirection]
  simp

@[simp] lemma corrCLM_cDirection (i : Fin 3) : corrCLM i cDirection =
    corrTriple 1 0 0 i := by
  rfl

@[simp] lemma corrCLM_betaDirection (i : Fin 3) : corrCLM i betaDirection = 0 := by
  fin_cases i <;> simp [corrCLM, betaDirection, corrTriple]

@[simp] lemma corrCLM_etaDirection (i : Fin 3) : corrCLM i etaDirection = 0 := by
  fin_cases i <;> simp [corrCLM, etaDirection, corrTriple]

@[simp] lemma corrCLM_leftEndpointDirection_one :
    corrCLM 1 leftEndpointDirection = 1 := by
  simp [corrCLM, leftEndpointDirection, corrTriple]

@[simp] lemma corrCLM_leftEndpointDirection_two :
    corrCLM 2 leftEndpointDirection = 0 := by
  simp [corrCLM, leftEndpointDirection, corrTriple]

@[simp] lemma corrCLM_rightEndpointDirection_one :
    corrCLM 1 rightEndpointDirection = 0 := by
  simp [corrCLM, rightEndpointDirection, corrTriple]

@[simp] lemma corrCLM_rightEndpointDirection_two :
    corrCLM 2 rightEndpointDirection = 1 := by
  simp [corrCLM, rightEndpointDirection, corrTriple]

/-- Evaluation in the normalization direction. -/
theorem splitIntegralFDeriv_cDirection
    (q : ℝ → ℝ) (hq : Continuous q) (c beta A B s : ℝ) :
    splitIntegralFDeriv q c beta A B s cDirection =
      ∫ x in A..B, q x * Real.exp (c + beta * x) := by
  rw [splitIntegralFDeriv_apply q hq]
  simp [corrTriple]
  have hc : Continuous (fun x ↦ q x * Real.exp (c + beta * x)) := by
    fun_prop
  exact intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable A s) (hc.intervalIntegrable s B)

/-- Evaluation in the unrestricted slope direction. -/
theorem splitIntegralFDeriv_betaDirection
    (q : ℝ → ℝ) (hq : Continuous q) (c beta A B s : ℝ) :
    splitIntegralFDeriv q c beta A B s betaDirection =
      ∫ x in A..B, q x * Real.exp (c + beta * x) * x := by
  rw [splitIntegralFDeriv_apply q hq]
  simp only [leftScore_betaDirection, rightScore_betaDirection,
    corrCLM_betaDirection, mul_zero, sub_zero, add_zero]
  have hc : Continuous (fun x ↦ q x * Real.exp (c + beta * x) * x) := by
    fun_prop
  exact intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (hc.intervalIntegrable A s) (hc.intervalIntegrable s B)

/-- Evaluation in the one-sided hinge direction. -/
theorem splitIntegralFDeriv_etaDirection
    (q : ℝ → ℝ) (hq : Continuous q) (c beta A B s : ℝ) :
    splitIntegralFDeriv q c beta A B s etaDirection =
      -∫ x in s..B, (x - s) * q x * Real.exp (c + beta * x) := by
  rw [splitIntegralFDeriv_apply q hq]
  simp only [leftScore_etaDirection, rightScore_etaDirection,
    corrCLM_etaDirection, mul_zero, intervalIntegral.integral_zero,
    zero_add, sub_zero, add_zero]
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro x _
  ring

/-- Evaluation in the left-endpoint direction. -/
theorem splitIntegralFDeriv_leftEndpointDirection
    (q : ℝ → ℝ) (hq : Continuous q) (c beta A B s : ℝ) :
    splitIntegralFDeriv q c beta A B s leftEndpointDirection =
      -q A * Real.exp (c + beta * A) := by
  rw [splitIntegralFDeriv_apply q hq]
  simp

/-- Evaluation in the right-endpoint direction. -/
theorem splitIntegralFDeriv_rightEndpointDirection
    (q : ℝ → ℝ) (hq : Continuous q) (c beta A B s : ℝ) :
    splitIntegralFDeriv q c beta A B s rightEndpointDirection =
      q B * Real.exp (c + beta * B) := by
  rw [splitIntegralFDeriv_apply q hq]
  simp


end LogConcaveExtremum.CompactSplitIntegral

/-! ## Flattened source: `lean_core/Variational.lean` -/


/-!
# Reusable finite-dimensional variational lemmas

This file contains the abstract calculus used by the compact-support cases of
the log-concave extremum argument.  The analytic work proving strict
differentiability of the concrete moment maps is kept in
`lean_core/ParametricInterval.lean`.
-/

open Filter Set
open scoped Topology

namespace LogConcaveExtremum.Variational

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The normal (non-abnormal) form of the Lagrange multiplier theorem.

Mathlib's theorem permits an additional multiplier in front of the objective.
Surjectivity of the constraint differential rules out the case in which that
multiplier vanishes, so it can be divided out.  We return an algebraic dual
functional because this is all the downstream residual argument needs; in the
finite-dimensional applications it is automatically continuous. -/
theorem normalized_lagrange
    {C : E → F} {φ : E → ℝ} {x₀ : E}
    {C' : E →L[ℝ] F} {φ' : StrongDual ℝ E}
    (hmax : IsLocalMaxOn φ {x | C x = C x₀} x₀)
    (hC : HasStrictFDerivAt C C' x₀)
    (hφ : HasStrictFDerivAt φ φ' x₀)
    (hCsurj : Function.Surjective C') :
    ∃ Λ : Module.Dual ℝ F, ∀ v, φ' v = Λ (C' v) := by
  obtain ⟨Λ, Λ₀, hne, hstationary⟩ :=
    IsLocalExtrOn.exists_linear_map_of_hasStrictFDerivAt hmax.isExtr hC hφ
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro hzero
    have hΛ : Λ = 0 := by
      apply LinearMap.ext
      intro y
      obtain ⟨v, rfl⟩ := hCsurj y
      simpa [hzero] using hstationary v
    exact hne (Prod.ext hΛ hzero)
  refine ⟨(-Λ₀⁻¹) • Λ, fun v => ?_⟩
  have hstat : Λ (C' v) + Λ₀ * φ' v = 0 := by
    simpa only [smul_eq_mul] using hstationary v
  have hprod : Λ₀ * φ' v = -Λ (C' v) :=
    eq_neg_of_add_eq_zero_right hstat
  have hinv : Λ₀⁻¹ * Λ₀ = 1 := inv_mul_cancel₀ hΛ₀
  simp only [LinearMap.smul_apply, smul_eq_mul]
  calc
    φ' v = Λ₀⁻¹ * (Λ₀ * φ' v) := by rw [← mul_assoc, hinv, one_mul]
    _ = Λ₀⁻¹ * (-Λ (C' v)) := by rw [hprod]
    _ = -Λ₀⁻¹ * Λ (C' v) := by ring

/-- A moment-preserving curve obtained from the product-domain implicit
function theorem.

The first factor is the free perturbation parameter and the second factor is
the correction variable.  The final formula is the derivative of the
correction curve. -/
theorem exists_feasibleCurve
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {u : P × E} {C : P × E → F} {C' : P × E →L[ℝ] F}
    (hC : HasStrictFDerivAt C C' u)
    (hcorrect : (C' ∘L ContinuousLinearMap.inr ℝ P E).IsInvertible) :
    ∃ ψ : P → E,
      ψ u.1 = u.2 ∧
      Tendsto ψ (𝓝 u.1) (𝓝 u.2) ∧
      (∀ᶠ p in 𝓝 u.1, C (p, ψ p) = C u) ∧
      HasStrictFDerivAt ψ
        (-(C' ∘L ContinuousLinearMap.inr ℝ P E).inverse ∘L
          (C' ∘L ContinuousLinearMap.inl ℝ P E)) u.1 := by
  let ψ := hC.implicitFunctionOfProdDomain hcorrect
  have hbase : ψ u.1 = u.2 :=
    (hC.eventually_apply_eq_iff_implicitFunctionOfProdDomain hcorrect).self_of_nhds.mp rfl
  exact ⟨ψ, hbase, hC.tendsto_implicitFunctionOfProdDomain hcorrect,
    hC.eventually_apply_implicitFunctionOfProdDomain hcorrect,
    hC.hasStrictFDerivAt_implicitFunctionOfProdDomain hcorrect⟩

/-- A one-sided feasible curve through a constrained local maximum has
nonpositive objective derivative.  This is the KKT sign needed for the hinge
parameter, whose admissible values satisfy `t ≥ 0`. -/
theorem oneSided_feasible_direction_nonpos
    {φ : E → ℝ} {S : Set E} {x₀ : E}
    {γ : ℝ → E} {d : ℝ}
    (hmax : IsLocalMaxOn φ S x₀)
    (hγ0 : γ 0 = x₀)
    (hγ : Tendsto γ (𝓝[Ici (0 : ℝ)] 0) (𝓝[S] x₀))
    (hderiv : HasDerivAt (φ ∘ γ) d 0) :
    d ≤ 0 := by
  have hmaxγ : IsLocalMaxOn (φ ∘ γ) (Ici (0 : ℝ)) 0 := by
    have hmax' : IsLocalMaxOn φ S (γ 0) := by simpa only [hγ0] using hmax
    have hγ' : Tendsto γ (𝓝[Ici (0 : ℝ)] 0) (𝓝[S] γ 0) := by
      simpa only [hγ0] using hγ
    exact hmax'.comp_tendsto hγ'
  have hone : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    exact (convex_Ici (0 : ℝ)).segment_subset (by simp) (by simp)
  have h := hmaxγ.hasFDerivWithinAt_nonpos
    hderiv.hasFDerivAt.hasFDerivWithinAt hone
  simpa using h

/-- The one-sided conclusion most useful in KKT arguments with a hinge
parameter.  The first coordinate is constrained to be nonnegative, while the
implicit-function theorem adjusts the second coordinate so that `C` remains
constant.  The displayed vector is the resulting feasible tangent at the
origin. -/
theorem oneSided_implicit_direction_nonpos
    {C : ℝ × E → F} {φ : ℝ × E → ℝ} {y₀ : E}
    {C' : ℝ × E →L[ℝ] F} {φ' : StrongDual ℝ (ℝ × E)}
    (hC : HasStrictFDerivAt C C' (0, y₀))
    (hφ : HasStrictFDerivAt φ φ' (0, y₀))
    (hcorrect : (C' ∘L ContinuousLinearMap.inr ℝ ℝ E).IsInvertible)
    (hmax : IsLocalMaxOn φ
      ({z | C z = C (0, y₀)} ∩ {z | 0 ≤ z.1}) (0, y₀)) :
    φ' ((ContinuousLinearMap.id ℝ ℝ).prod
      (-(C' ∘L ContinuousLinearMap.inr ℝ ℝ E).inverse ∘L
        (C' ∘L ContinuousLinearMap.inl ℝ ℝ E)) 1) ≤ 0 := by
  let Dψ : ℝ →L[ℝ] E :=
    -(C' ∘L ContinuousLinearMap.inr ℝ ℝ E).inverse ∘L
      (C' ∘L ContinuousLinearMap.inl ℝ ℝ E)
  let ψ : ℝ → E := hC.implicitFunctionOfProdDomain hcorrect
  let γ : ℝ → ℝ × E := fun t ↦ (t, ψ t)
  have hψ0 : ψ 0 = y₀ := by
    exact (hC.eventually_apply_eq_iff_implicitFunctionOfProdDomain hcorrect).self_of_nhds.mp rfl
  have hγ0 : γ 0 = (0, y₀) := by
    simp only [γ, hψ0]
  have hψderiv : HasStrictFDerivAt ψ Dψ 0 := by
    exact hC.hasStrictFDerivAt_implicitFunctionOfProdDomain hcorrect
  have hγderiv : HasStrictFDerivAt γ
      ((ContinuousLinearMap.id ℝ ℝ).prod Dψ) 0 := by
    exact (hasStrictFDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))).prodMk hψderiv
  have hγfeasible : Tendsto γ (𝓝[Ici (0 : ℝ)] 0)
      (𝓝[({z | C z = C (0, y₀)} ∩ {z | 0 ≤ z.1})] (0, y₀)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht : Tendsto γ (𝓝[Ici (0 : ℝ)] 0) (𝓝 (γ 0)) :=
        hγderiv.continuousAt.tendsto.mono_left inf_le_left
      simpa only [hγ0] using ht
    · have hCeq : ∀ᶠ t in 𝓝 (0 : ℝ), C (t, ψ t) = C (0, y₀) :=
        hC.eventually_apply_implicitFunctionOfProdDomain hcorrect
      filter_upwards [hCeq.filter_mono inf_le_left, self_mem_nhdsWithin] with t htC ht
      exact ⟨htC, ht⟩
  have hcomp : HasDerivAt (φ ∘ γ)
      (φ' (((ContinuousLinearMap.id ℝ ℝ).prod Dψ) 1)) 0 :=
    have hφ_at : HasStrictFDerivAt φ φ' (γ 0) := by simpa only [hγ0] using hφ
    (hφ_at.comp (0 : ℝ) hγderiv).hasStrictDerivAt.hasDerivAt
  have hnonpos := oneSided_feasible_direction_nonpos hmax hγ0 hγfeasible hcomp
  simpa only [Dψ] using hnonpos

/-- Two free parameters with the second constrained to be nonnegative.

This is the form used for a slope perturbation together with a one-sided
hinge perturbation.  An implicit function corrects the remaining variables.
At a constrained local maximum the reduced derivative vanishes in the first
free direction and is nonpositive in the second. -/
theorem twoParameter_implicit_stationarity
    {C : (ℝ × ℝ) × E → F} {φ : (ℝ × ℝ) × E → ℝ} {y₀ : E}
    {C' : (ℝ × ℝ) × E →L[ℝ] F} {φ' : StrongDual ℝ ((ℝ × ℝ) × E)}
    (hC : HasStrictFDerivAt C C' ((0, 0), y₀))
    (hφ : HasStrictFDerivAt φ φ' ((0, 0), y₀))
    (hcorrect :
      (C' ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) E).IsInvertible)
    (hmax : IsLocalMaxOn φ
      ({z | C z = C ((0, 0), y₀)} ∩ {z | 0 ≤ z.1.2}) ((0, 0), y₀)) :
    let Dψ :=
      -(C' ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) E).inverse ∘L
        (C' ∘L ContinuousLinearMap.inl ℝ (ℝ × ℝ) E)
    let Dgraph := (ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod Dψ
    φ' (Dgraph (1, 0)) = 0 ∧ φ' (Dgraph (0, 1)) ≤ 0 := by
  let Dψ : (ℝ × ℝ) →L[ℝ] E :=
    -(C' ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) E).inverse ∘L
      (C' ∘L ContinuousLinearMap.inl ℝ (ℝ × ℝ) E)
  let ψ : (ℝ × ℝ) → E := hC.implicitFunctionOfProdDomain hcorrect
  let graph : (ℝ × ℝ) → (ℝ × ℝ) × E := fun p ↦ (p, ψ p)
  let reduced : (ℝ × ℝ) → ℝ := φ ∘ graph
  let Pplus : Set (ℝ × ℝ) := {p | 0 ≤ p.2}
  have hψ0 : ψ (0, 0) = y₀ := by
    exact (hC.eventually_apply_eq_iff_implicitFunctionOfProdDomain hcorrect).self_of_nhds.mp rfl
  have hgraph0 : graph (0, 0) = ((0, 0), y₀) := by
    simp only [graph, hψ0]
  have hψderiv : HasStrictFDerivAt ψ Dψ (0, 0) := by
    exact hC.hasStrictFDerivAt_implicitFunctionOfProdDomain hcorrect
  have hgraphderiv : HasStrictFDerivAt graph
      ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod Dψ) (0, 0) := by
    exact (hasStrictFDerivAt_id (𝕜 := ℝ) (x := (0, 0))).prodMk hψderiv
  have hreducedderiv : HasStrictFDerivAt reduced
      (φ'.comp ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod Dψ)) (0, 0) := by
    have hφ_at : HasStrictFDerivAt φ φ' (graph (0, 0)) := by
      simpa only [hgraph0] using hφ
    exact hφ_at.comp ((0 : ℝ), (0 : ℝ)) hgraphderiv
  have hgraphfeasible : Tendsto graph (𝓝[Pplus] (0, 0))
      (𝓝[({z | C z = C ((0, 0), y₀)} ∩ {z | 0 ≤ z.1.2})] ((0, 0), y₀)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht : Tendsto graph (𝓝[Pplus] (0, 0)) (𝓝 (graph (0, 0))) :=
        hgraphderiv.continuousAt.tendsto.mono_left inf_le_left
      simpa only [hgraph0] using ht
    · have hCeq : ∀ᶠ p in 𝓝 (0, 0), C (p, ψ p) = C ((0, 0), y₀) :=
        hC.eventually_apply_implicitFunctionOfProdDomain hcorrect
      filter_upwards [hCeq.filter_mono inf_le_left, self_mem_nhdsWithin] with p hpC hp
      exact ⟨hpC, hp⟩
  have hmaxReduced : IsLocalMaxOn reduced Pplus (0, 0) := by
    have hmax' : IsLocalMaxOn φ
        ({z | C z = C ((0, 0), y₀)} ∩ {z | 0 ≤ z.1.2}) (graph (0, 0)) := by
      simpa only [hgraph0] using hmax
    have ht : Tendsto graph (𝓝[Pplus] (0, 0))
        (𝓝[({z | C z = C ((0, 0), y₀)} ∩ {z | 0 ≤ z.1.2})] graph (0, 0)) := by
      simpa only [hgraph0] using hgraphfeasible
    exact hmax'.comp_tendsto ht
  let βline : ℝ → ℝ × ℝ := fun t ↦ (t, 0)
  let ηline : ℝ → ℝ × ℝ := fun t ↦ (0, t)
  let Dβ : ℝ →L[ℝ] ℝ × ℝ :=
    (ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)
  let Dη : ℝ →L[ℝ] ℝ × ℝ :=
    (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)
  have hβline : HasStrictFDerivAt βline Dβ 0 := by
    simpa [βline, Dβ] using
      ((hasStrictFDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))).prodMk
        (hasStrictFDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))))
  have hηline : HasStrictFDerivAt ηline Dη 0 := by
    simpa [ηline, Dη] using
      ((hasStrictFDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))).prodMk
        (hasStrictFDerivAt_id (𝕜 := ℝ) (x := (0 : ℝ))))
  have hβfeasible : Tendsto βline (𝓝 (0 : ℝ)) (𝓝[Pplus] (0, 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [βline] using hβline.continuousAt.tendsto
    · filter_upwards [] with t
      simp [Pplus, βline]
  have hηfeasible : Tendsto ηline (𝓝[Ici (0 : ℝ)] 0) (𝓝[Pplus] (0, 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht : Tendsto ηline (𝓝[Ici (0 : ℝ)] 0) (𝓝 (ηline 0)) :=
        hηline.continuousAt.tendsto.mono_left inf_le_left
      simpa [ηline] using ht
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa [Pplus, ηline] using ht
  have hβmax : IsLocalMax (reduced ∘ βline) 0 := by
    exact hmaxReduced.comp_tendsto (g := βline) hβfeasible
  have hβderiv : HasDerivAt (reduced ∘ βline)
      ((φ'.comp ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod Dψ)) (1, 0)) 0 := by
    change HasDerivAt (fun t : ℝ ↦ reduced (t, 0))
      ((φ'.comp ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod Dψ)) (1, 0)) 0
    have hr_at : HasStrictFDerivAt reduced
        (φ'.comp ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod Dψ)) (βline 0) := by
      simpa [βline] using hreducedderiv
    simpa [Function.comp_apply, ContinuousLinearMap.comp_apply, βline, Dβ] using
      (hr_at.comp (0 : ℝ) hβline).hasStrictDerivAt.hasDerivAt
  have hηderiv : HasDerivAt (reduced ∘ ηline)
      ((φ'.comp ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod Dψ)) (0, 1)) 0 := by
    change HasDerivAt (fun t : ℝ ↦ reduced (0, t))
      ((φ'.comp ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod Dψ)) (0, 1)) 0
    have hr_at : HasStrictFDerivAt reduced
        (φ'.comp ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod Dψ)) (ηline 0) := by
      simpa [ηline] using hreducedderiv
    simpa [Function.comp_apply, ContinuousLinearMap.comp_apply, ηline, Dη] using
      (hr_at.comp (0 : ℝ) hηline).hasStrictDerivAt.hasDerivAt
  constructor
  · simpa only [ContinuousLinearMap.comp_apply] using hβmax.hasDerivAt_eq_zero hβderiv
  · have hη := oneSided_feasible_direction_nonpos hmaxReduced
      (show ηline 0 = (0, 0) by simp [ηline]) hηfeasible hηderiv
    simpa only [ContinuousLinearMap.comp_apply] using hη

/-- The canonical multiplier obtained by solving the correction equations. -/
noncomputable def canonicalMultiplier
    (C' : (ℝ × ℝ) × E →L[ℝ] F)
    (φ' : StrongDual ℝ ((ℝ × ℝ) × E)) : StrongDual ℝ F :=
  φ'.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) E ∘L
    (C' ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) E).inverse)

/-- Canonical (hence reusable) multiplier form of
`twoParameter_implicit_stationarity`.

Unlike an existential multiplier statement, this theorem identifies the
multiplier explicitly from the correction derivative.  Thus, if several
one-sided perturbations have the same objective derivative and the same
correction block, the multiplier is definitionally the same for all of them. -/
theorem twoParameter_canonical_multiplier_stationarity
    {C : (ℝ × ℝ) × E → F} {φ : (ℝ × ℝ) × E → ℝ} {y₀ : E}
    {C' : (ℝ × ℝ) × E →L[ℝ] F} {φ' : StrongDual ℝ ((ℝ × ℝ) × E)}
    (hC : HasStrictFDerivAt C C' ((0, 0), y₀))
    (hφ : HasStrictFDerivAt φ φ' ((0, 0), y₀))
    (hcorrect :
      (C' ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) E).IsInvertible)
    (hmax : IsLocalMaxOn φ
      ({z | C z = C ((0, 0), y₀)} ∩ {z | 0 ≤ z.1.2}) ((0, 0), y₀)) :
    (∀ e : E, φ' ((0, 0), e) =
      canonicalMultiplier C' φ' (C' ((0, 0), e))) ∧
    φ' (((1, 0), 0)) =
      canonicalMultiplier C' φ' (C' (((1, 0), 0))) ∧
    φ' (((0, 1), 0)) ≤
      canonicalMultiplier C' φ' (C' (((0, 1), 0))) := by
  let D : E →L[ℝ] F := C' ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) E
  let B : (ℝ × ℝ) →L[ℝ] F := C' ∘L ContinuousLinearMap.inl ℝ (ℝ × ℝ) E
  let Λ : StrongDual ℝ F := canonicalMultiplier C' φ'
  have hD : D.IsInvertible := by simpa only [D] using hcorrect
  have hΛ : Λ =
      φ'.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) E ∘L D.inverse) := by
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro e
    change φ' ((0, 0), e) = Λ (D e)
    rw [hΛ]
    change φ' ((0, 0), e) = φ' ((0, 0), D.inverse (D e))
    rw [hD.inverse_apply_self]
  · have hred := (twoParameter_implicit_stationarity hC hφ hcorrect hmax).1
    have hdecomp :
        φ' (((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod
          (-(D.inverse) ∘L B)) (1, 0)) =
          φ' (((1, 0), 0)) - Λ (B (1, 0)) := by
      rw [hΛ]
      change φ' (((1, 0), -D.inverse (B (1, 0)))) =
        φ' (((1, 0), 0)) - φ' ((0, 0), D.inverse (B (1, 0)))
      have hv : (((1, 0), -D.inverse (B (1, 0))) : (ℝ × ℝ) × E) =
          ((1, 0), 0) - ((0, 0), D.inverse (B (1, 0))) := by
        ext <;> simp
      rw [hv, map_sub]
    rw [hdecomp] at hred
    have heq : φ' (((1, 0), 0)) = Λ (B (1, 0)) := sub_eq_zero.mp hred
    simpa [Λ, B, canonicalMultiplier, ContinuousLinearMap.comp_apply] using heq
  · have hred := (twoParameter_implicit_stationarity hC hφ hcorrect hmax).2
    have hdecomp :
        φ' (((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod
          (-(D.inverse) ∘L B)) (0, 1)) =
          φ' (((0, 1), 0)) - Λ (B (0, 1)) := by
      rw [hΛ]
      change φ' (((0, 1), -D.inverse (B (0, 1)))) =
        φ' (((0, 1), 0)) - φ' ((0, 0), D.inverse (B (0, 1)))
      have hv : (((0, 1), -D.inverse (B (0, 1))) : (ℝ × ℝ) × E) =
          ((0, 1), 0) - ((0, 0), D.inverse (B (0, 1))) := by
        ext <;> simp
      rw [hv, map_sub]
    rw [hdecomp] at hred
    have hle : φ' (((0, 1), 0)) ≤ Λ (B (0, 1)) := sub_nonpos.mp hred
    simpa [Λ, B, canonicalMultiplier, ContinuousLinearMap.comp_apply] using hle

/-- Multiplier form of `twoParameter_implicit_stationarity`.

The multiplier is constructed, rather than obtained from a second Lagrange
theorem, by inverting the correction derivative.  It gives equality in all
correction directions and in the unrestricted first free direction, and the
KKT inequality in the one-sided second free direction. -/
theorem twoParameter_multiplier_stationarity
    {C : (ℝ × ℝ) × E → F} {φ : (ℝ × ℝ) × E → ℝ} {y₀ : E}
    {C' : (ℝ × ℝ) × E →L[ℝ] F} {φ' : StrongDual ℝ ((ℝ × ℝ) × E)}
    (hC : HasStrictFDerivAt C C' ((0, 0), y₀))
    (hφ : HasStrictFDerivAt φ φ' ((0, 0), y₀))
    (hcorrect :
      (C' ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) E).IsInvertible)
    (hmax : IsLocalMaxOn φ
      ({z | C z = C ((0, 0), y₀)} ∩ {z | 0 ≤ z.1.2}) ((0, 0), y₀)) :
    ∃ Λ : StrongDual ℝ F,
      (∀ e : E, φ' ((0, 0), e) = Λ (C' ((0, 0), e))) ∧
      φ' (((1, 0), 0)) = Λ (C' (((1, 0), 0))) ∧
      φ' (((0, 1), 0)) ≤ Λ (C' (((0, 1), 0))) := by
  let D : E →L[ℝ] F := C' ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) E
  let B : (ℝ × ℝ) →L[ℝ] F := C' ∘L ContinuousLinearMap.inl ℝ (ℝ × ℝ) E
  let Λ : StrongDual ℝ F :=
    φ'.comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) E ∘L D.inverse)
  have hD : D.IsInvertible := by simpa only [D] using hcorrect
  refine ⟨Λ, ?_, ?_, ?_⟩
  · intro e
    change φ' ((0, 0), e) = φ' ((0, 0), D.inverse (D e))
    rw [hD.inverse_apply_self]
  · have hred := (twoParameter_implicit_stationarity hC hφ hcorrect hmax).1
    have hdecomp :
        φ' (((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod
          (-(D.inverse) ∘L B)) (1, 0)) =
          φ' (((1, 0), 0)) - Λ (B (1, 0)) := by
      change φ' (((1, 0), -D.inverse (B (1, 0)))) =
        φ' (((1, 0), 0)) - φ' ((0, 0), D.inverse (B (1, 0)))
      have hv : (((1, 0), -D.inverse (B (1, 0))) : (ℝ × ℝ) × E) =
          ((1, 0), 0) - ((0, 0), D.inverse (B (1, 0))) := by
        ext <;> simp
      rw [hv, map_sub]
    rw [hdecomp] at hred
    have : φ' (((1, 0), 0)) = Λ (B (1, 0)) := sub_eq_zero.mp hred
    simpa [B, ContinuousLinearMap.comp_apply] using this
  · have hred := (twoParameter_implicit_stationarity hC hφ hcorrect hmax).2
    have hdecomp :
        φ' (((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod
          (-(D.inverse) ∘L B)) (0, 1)) =
          φ' (((0, 1), 0)) - Λ (B (0, 1)) := by
      change φ' (((0, 1), -D.inverse (B (0, 1)))) =
        φ' (((0, 1), 0)) - φ' ((0, 0), D.inverse (B (0, 1)))
      have hv : (((0, 1), -D.inverse (B (0, 1))) : (ℝ × ℝ) × E) =
          ((0, 1), 0) - ((0, 0), D.inverse (B (0, 1))) := by
        ext <;> simp
      rw [hv, map_sub]
    rw [hdecomp] at hred
    have := sub_nonpos.mp hred
    simpa [B, ContinuousLinearMap.comp_apply] using this

end LogConcaveExtremum.Variational

/-! ## Flattened source: `lean_ii/Jacobian.lean` -/


open Set

namespace CompactOnePiece

/-- For a positive probability density on `[A,B]` with mean zero and second
moment one, the endpoint product is strictly smaller than `-1`.  This is the
nonvanishing determinant needed for the three correcting variables
`(c,A,B)` in the hinge perturbation. -/
theorem one_add_endpoints_mul_neg
    {w : ℝ → ℝ} {A B : ℝ}
    (hAB : A < B) (hw : Continuous w) (hwpos : ∀ x, 0 < w x)
    (hmass : (∫ x in A..B, w x) = 1)
    (hmean : (∫ x in A..B, x * w x) = 0)
    (hsecond : (∫ x in A..B, x ^ 2 * w x) = 1) :
    1 + A * B < 0 := by
  let P : ℝ → ℝ := fun x ↦ (x - A) * (B - x) * w x
  have hP : Continuous P := by
    dsimp [P]
    fun_prop
  have hPnonneg : ∀ x ∈ Ioc A B, 0 ≤ P x := by
    intro x hx
    dsimp [P]
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hx.1.le) (sub_nonneg.mpr hx.2))
      (hwpos x).le
  let m := (A + B) / 2
  have hm : m ∈ Icc A B := by
    dsimp [m]
    constructor <;> linarith
  have hPm : 0 < P m := by
    dsimp [P, m]
    have hleft : 0 < (A + B) / 2 - A := by linarith
    have hright : 0 < B - (A + B) / 2 := by linarith
    exact mul_pos (mul_pos hleft hright) (hwpos ((A + B) / 2))
  have hPint : 0 < ∫ x in A..B, P x := by
    exact intervalIntegral.integral_pos hAB hP.continuousOn hPnonneg ⟨m, hm, hPm⟩
  have hW : IntervalIntegrable w MeasureTheory.volume A B := hw.intervalIntegrable A B
  have hX : IntervalIntegrable (fun x ↦ x * w x) MeasureTheory.volume A B :=
    (continuous_id.mul hw).intervalIntegrable A B
  have hX2 : IntervalIntegrable (fun x ↦ x ^ 2 * w x) MeasureTheory.volume A B :=
    ((continuous_id.pow 2).mul hw).intervalIntegrable A B
  have hpoint : P = fun x ↦
      -(x ^ 2 * w x) + (A + B) * (x * w x) - (A * B) * w x := by
    funext x
    dsimp [P]
    ring
  rw [hpoint] at hPint
  have houter := intervalIntegral.integral_sub
    ((hX2.neg).add (hX.const_mul (A + B))) (hW.const_mul (A * B))
  change
    (∫ x in A..B,
      (-(x ^ 2 * w x) + (A + B) * (x * w x)) - (A * B) * w x) =
      (∫ x in A..B, -(x ^ 2 * w x) + (A + B) * (x * w x)) -
        ∫ x in A..B, (A * B) * w x at houter
  have hinner := intervalIntegral.integral_add hX2.neg (hX.const_mul (A + B))
  change
    (∫ x in A..B, -(x ^ 2 * w x) + (A + B) * (x * w x)) =
      (∫ x in A..B, -(x ^ 2 * w x)) +
        ∫ x in A..B, (A + B) * (x * w x) at hinner
  rw [houter, hinner, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hmass, hmean, hsecond] at hPint
  linarith

/-- Algebraic nonsingularity of the `(c,A,B)` moment Jacobian.  The three
equations are its mass, mean, and second-moment rows. -/
theorem corrector_jacobian_kernel
    {A B wA wB dc dA dB : ℝ}
    (hAB : A < B) (hprod : 1 + A * B ≠ 0)
    (hwA : wA ≠ 0) (hwB : wB ≠ 0)
    (h0 : dc - wA * dA + wB * dB = 0)
    (h1 : -A * wA * dA + B * wB * dB = 0)
    (h2 : dc - A ^ 2 * wA * dA + B ^ 2 * wB * dB = 0) :
    dc = 0 ∧ dA = 0 ∧ dB = 0 := by
  have hdet : (B - A) * (1 + A * B) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hAB.ne') hprod
  have hp : ((B - A) * (1 + A * B)) * (wA * dA) = 0 := by
    linear_combination B * (h2 - h0) - (B ^ 2 - 1) * h1
  have hq : ((B - A) * (1 + A * B)) * (wB * dB) = 0 := by
    linear_combination A * (h2 - h0) - (A ^ 2 - 1) * h1
  have hWA : wA * dA = 0 := (mul_eq_zero.mp hp).resolve_left hdet
  have hWB : wB * dB = 0 := (mul_eq_zero.mp hq).resolve_left hdet
  have hdA : dA = 0 := (mul_eq_zero.mp hWA).resolve_left hwA
  have hdB : dB = 0 := (mul_eq_zero.mp hWB).resolve_left hwB
  subst dA
  subst dB
  simp only [mul_zero, sub_zero, add_zero] at h0
  exact ⟨h0, rfl, rfl⟩

end CompactOnePiece

/-! ## Flattened source: `lean_core/CompactMomentMap.lean` -/


/-!
# Moment map and its invertible correction block

This file packages the mass, mean, and second-moment constraints for the
compact split variation and proves that the `(c,A,B)` correction block is
invertible at an isotropic positive log-affine density.
-/

open Set MeasureTheory
open scoped Topology Interval

namespace LogConcaveExtremum.CompactMomentMap

open CompactSplitIntegral


/-- The three test functions `1`, `x`, and `x²`. -/
def momentTest (i : Fin 3) (x : ℝ) : ℝ :=
  Fin.cases (1 : ℝ) (Fin.cases x (fun _ ↦ x ^ 2)) i

lemma continuous_momentTest (i : Fin 3) : Continuous (momentTest i) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact continuous_const
  · refine Fin.cases ?_ (fun _ ↦ ?_) j
    · exact continuous_id
    · exact continuous_id.pow 2

@[simp] lemma momentTest_zero (x : ℝ) : momentTest 0 x = 1 := rfl
@[simp] lemma momentTest_one (x : ℝ) : momentTest 1 x = x := rfl
@[simp] lemma momentTest_two (x : ℝ) : momentTest 2 x = x ^ 2 := rfl

/-- Mass, first moment, and second moment of the split variation. -/
def momentMap (beta s : ℝ) (p : Param) : Corr :=
  fun i ↦ splitIntegral (momentTest i) beta s p

/-- Derivative of the three moment constraints. -/
def momentFDeriv (c beta A B s : ℝ) : Param →L[ℝ] Corr :=
  ContinuousLinearMap.pi
    (fun i ↦ splitIntegralFDeriv (momentTest i) c beta A B s)

@[simp] theorem momentFDeriv_apply
    (c beta A B s : ℝ) (v : Param) (i : Fin 3) :
    momentFDeriv c beta A B s v i =
      splitIntegralFDeriv (momentTest i) c beta A B s v := by
  simp [momentFDeriv]

theorem momentMap_base (c beta A B s : ℝ) :
    momentMap beta s (baseParam c A B) =
      fun i ↦ ∫ x in A..B, momentTest i x * Real.exp (c + beta * x) := by
  funext i
  exact splitIntegral_base (momentTest i) (continuous_momentTest i) c beta A B s

theorem momentFDeriv_cDirection (c beta A B s : ℝ) :
    momentFDeriv c beta A B s cDirection =
      fun i ↦ ∫ x in A..B, momentTest i x * Real.exp (c + beta * x) := by
  funext i
  rw [momentFDeriv_apply,
    splitIntegralFDeriv_cDirection (momentTest i) (continuous_momentTest i)]

theorem momentFDeriv_betaDirection (c beta A B s : ℝ) :
    momentFDeriv c beta A B s betaDirection =
      fun i ↦ ∫ x in A..B,
        momentTest i x * Real.exp (c + beta * x) * x := by
  funext i
  rw [momentFDeriv_apply,
    splitIntegralFDeriv_betaDirection (momentTest i) (continuous_momentTest i)]

theorem momentFDeriv_etaDirection (c beta A B s : ℝ) :
    momentFDeriv c beta A B s etaDirection =
      fun i ↦ -∫ x in s..B,
        (x - s) * momentTest i x * Real.exp (c + beta * x) := by
  funext i
  rw [momentFDeriv_apply,
    splitIntegralFDeriv_etaDirection (momentTest i) (continuous_momentTest i)]

theorem momentFDeriv_leftEndpointDirection (c beta A B s : ℝ) :
    momentFDeriv c beta A B s leftEndpointDirection =
      fun i ↦ -momentTest i A * Real.exp (c + beta * A) := by
  funext i
  rw [momentFDeriv_apply,
    splitIntegralFDeriv_leftEndpointDirection (momentTest i) (continuous_momentTest i)]

theorem momentFDeriv_rightEndpointDirection (c beta A B s : ℝ) :
    momentFDeriv c beta A B s rightEndpointDirection =
      fun i ↦ momentTest i B * Real.exp (c + beta * B) := by
  funext i
  rw [momentFDeriv_apply,
    splitIntegralFDeriv_rightEndpointDirection (momentTest i) (continuous_momentTest i)]

/-- Strict derivative with all norm-induced structures selected explicitly. -/
abbrev HasStrictParamCorrFDerivAt
    (f : Param → Corr) (f' : Param →L[ℝ] Corr) (p : Param) : Prop :=
  @HasStrictFDerivAt ℝ DenselyNormedField.toNontriviallyNormedField Param
    Prod.normedAddCommGroup.toAddCommGroup
    Prod.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    Corr Pi.normedAddCommGroup.toAddCommGroup
    Pi.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    f f' p

theorem hasStrictFDerivAt_momentMap
    (c beta A B s : ℝ) :
    HasStrictParamCorrFDerivAt (momentMap beta s)
      (momentFDeriv c beta A B s) (baseParam c A B) := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  exact hasStrictFDerivAt_splitIntegral
    (momentTest i) (continuous_momentTest i) c beta A B s

/-- The restriction of the moment derivative to the correction variables
`(c,A,B)`. -/
def momentCorrectionBlock (c beta A B s : ℝ) : Corr →L[ℝ] Corr :=
  momentFDeriv c beta A B s ∘L ContinuousLinearMap.inr ℝ Free Corr

lemma correction_direction_decomposition (e : Corr) :
    (((0, 0), e) : Param) =
      e 0 • cDirection + e 1 • leftEndpointDirection +
        e 2 • rightEndpointDirection := by
  apply Prod.ext
  · ext <;> simp [cDirection, leftEndpointDirection, rightEndpointDirection]
  · funext i
    fin_cases i <;>
      simp [cDirection, leftEndpointDirection, rightEndpointDirection, corrTriple]

/-- Correction-direction derivative for an arbitrary continuous test
function. -/
theorem splitIntegralFDeriv_correction_apply
    (q : ℝ → ℝ) (hq : Continuous q)
    (c beta A B s : ℝ) (e : Corr) :
    splitIntegralFDeriv q c beta A B s (((0, 0), e) : Param) =
      e 0 * (∫ x in A..B, q x * Real.exp (c + beta * x)) -
      e 1 * (q A * Real.exp (c + beta * A)) +
      e 2 * (q B * Real.exp (c + beta * B)) := by
  have h := congrArg (splitIntegralFDeriv q c beta A B s)
    (correction_direction_decomposition e)
  simp only [map_add, map_smul] at h
  rw [splitIntegralFDeriv_cDirection q hq,
    splitIntegralFDeriv_leftEndpointDirection q hq,
    splitIntegralFDeriv_rightEndpointDirection q hq] at h
  rw [h]
  ring

/-- The objective derivative restricted to `(c,A,B)` does not depend on the
chosen hinge point. -/
theorem splitIntegralFDeriv_comp_inr_eq
    (q : ℝ → ℝ) (hq : Continuous q)
    (c beta A B s t : ℝ) :
    splitIntegralFDeriv q c beta A B s ∘L
        ContinuousLinearMap.inr ℝ Free Corr =
      splitIntegralFDeriv q c beta A B t ∘L
        ContinuousLinearMap.inr ℝ Free Corr := by
  apply ContinuousLinearMap.ext
  intro e
  simp only [ContinuousLinearMap.comp_apply]
  change splitIntegralFDeriv q c beta A B s (((0, 0), e) : Param) =
    splitIntegralFDeriv q c beta A B t (((0, 0), e) : Param)
  rw [splitIntegralFDeriv_correction_apply q hq,
    splitIntegralFDeriv_correction_apply q hq]

/-- The moment correction block is independent of the hinge point. -/
theorem momentCorrectionBlock_eq
    (c beta A B s t : ℝ) :
    momentCorrectionBlock c beta A B s =
      momentCorrectionBlock c beta A B t := by
  unfold momentCorrectionBlock momentFDeriv
  apply ContinuousLinearMap.ext
  intro e
  funext i
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply]
  change splitIntegralFDeriv (momentTest i) c beta A B s (((0, 0), e) : Param) =
    splitIntegralFDeriv (momentTest i) c beta A B t (((0, 0), e) : Param)
  rw [splitIntegralFDeriv_correction_apply (momentTest i) (continuous_momentTest i),
    splitIntegralFDeriv_correction_apply (momentTest i) (continuous_momentTest i)]

/-- Consequently the canonical Lagrange multiplier is the same for every
hinge point. -/
theorem canonicalMultiplier_moment_eq
    (q : ℝ → ℝ) (hq : Continuous q)
    (c beta A B s t : ℝ) :
    Variational.canonicalMultiplier
        (momentFDeriv c beta A B s)
        (splitIntegralFDeriv q c beta A B s) =
      Variational.canonicalMultiplier
        (momentFDeriv c beta A B t)
        (splitIntegralFDeriv q c beta A B t) := by
  apply ContinuousLinearMap.ext
  intro y
  unfold Variational.canonicalMultiplier
  simp only [ContinuousLinearMap.comp_apply]
  have hD :
      momentFDeriv c beta A B s ∘L ContinuousLinearMap.inr ℝ Free Corr =
        momentFDeriv c beta A B t ∘L ContinuousLinearMap.inr ℝ Free Corr := by
    exact momentCorrectionBlock_eq c beta A B s t
  rw [hD]
  have hφ := congrArg
    (fun L : Corr →L[ℝ] ℝ ↦
      L ((momentFDeriv c beta A B t ∘L
        ContinuousLinearMap.inr ℝ Free Corr).inverse y))
    (splitIntegralFDeriv_comp_inr_eq q hq c beta A B s t)
  simpa only [ContinuousLinearMap.comp_apply] using hφ

theorem momentCorrectionBlock_apply_zero
    (c beta A B s : ℝ)
    (hmass : (∫ x in A..B, Real.exp (c + beta * x)) = 1)
    (e : Corr) :
    momentCorrectionBlock c beta A B s e 0 =
      e 0 - Real.exp (c + beta * A) * e 1 +
        Real.exp (c + beta * B) * e 2 := by
  unfold momentCorrectionBlock momentFDeriv
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply]
  change splitIntegralFDeriv (momentTest 0) c beta A B s (((0, 0), e) : Param) = _
  rw [splitIntegralFDeriv_correction_apply (momentTest 0) (continuous_momentTest 0)]
  simp only [momentTest_zero, one_mul, hmass]
  ring

theorem momentCorrectionBlock_apply_one
    (c beta A B s : ℝ)
    (hmean : (∫ x in A..B, x * Real.exp (c + beta * x)) = 0)
    (e : Corr) :
    momentCorrectionBlock c beta A B s e 1 =
      -A * Real.exp (c + beta * A) * e 1 +
        B * Real.exp (c + beta * B) * e 2 := by
  unfold momentCorrectionBlock momentFDeriv
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply]
  change splitIntegralFDeriv (momentTest 1) c beta A B s (((0, 0), e) : Param) = _
  rw [splitIntegralFDeriv_correction_apply (momentTest 1) (continuous_momentTest 1)]
  simp only [momentTest_one]
  rw [hmean]
  ring

theorem momentCorrectionBlock_apply_two
    (c beta A B s : ℝ)
    (hsecond : (∫ x in A..B, x ^ 2 * Real.exp (c + beta * x)) = 1)
    (e : Corr) :
    momentCorrectionBlock c beta A B s e 2 =
      e 0 - A ^ 2 * Real.exp (c + beta * A) * e 1 +
        B ^ 2 * Real.exp (c + beta * B) * e 2 := by
  unfold momentCorrectionBlock momentFDeriv
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply]
  change splitIntegralFDeriv (momentTest 2) c beta A B s (((0, 0), e) : Param) = _
  rw [splitIntegralFDeriv_correction_apply (momentTest 2) (continuous_momentTest 2)]
  simp only [momentTest_two, hsecond]
  ring

/-- The `(c,A,B)` correction block is invertible at every isotropic positive
log-affine density on a nondegenerate compact interval. -/
theorem momentCorrectionBlock_isInvertible
    (c beta A B s : ℝ) (hAB : A < B)
    (hmass : (∫ x in A..B, Real.exp (c + beta * x)) = 1)
    (hmean : (∫ x in A..B, x * Real.exp (c + beta * x)) = 0)
    (hsecond : (∫ x in A..B, x ^ 2 * Real.exp (c + beta * x)) = 1) :
    (momentCorrectionBlock c beta A B s).IsInvertible := by
  let D := momentCorrectionBlock c beta A B s
  have hwcont : Continuous (fun x : ℝ ↦ Real.exp (c + beta * x)) := by
    fun_prop
  have hwpos : ∀ x : ℝ, 0 < Real.exp (c + beta * x) :=
    fun x ↦ Real.exp_pos _
  have hprodlt : 1 + A * B < 0 :=
    CompactOnePiece.one_add_endpoints_mul_neg hAB hwcont hwpos
      hmass hmean hsecond
  have hprod : 1 + A * B ≠ 0 := ne_of_lt hprodlt
  have hzero : ∀ e : Corr, D e = 0 → e = 0 := by
    intro e he
    have he0 := congrFun he 0
    have he1 := congrFun he 1
    have he2 := congrFun he 2
    change momentCorrectionBlock c beta A B s e 0 = 0 at he0
    change momentCorrectionBlock c beta A B s e 1 = 0 at he1
    change momentCorrectionBlock c beta A B s e 2 = 0 at he2
    rw [momentCorrectionBlock_apply_zero c beta A B s hmass] at he0
    rw [momentCorrectionBlock_apply_one c beta A B s hmean] at he1
    rw [momentCorrectionBlock_apply_two c beta A B s hsecond] at he2
    obtain ⟨hc, hA, hB⟩ := CompactOnePiece.corrector_jacobian_kernel
      hAB hprod (Real.exp_ne_zero _) (Real.exp_ne_zero _)
      (by simpa [mul_comm] using he0)
      (by simpa [mul_comm] using he1)
      (by simpa [mul_comm] using he2)
    funext i
    fin_cases i
    · exact hc
    · exact hA
    · exact hB
  have hker : D.ker = ⊥ := LinearMap.ker_eq_bot'.mpr hzero
  have hrange : D.range = ⊤ :=
    (LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank
      (show Module.finrank ℝ Corr = Module.finrank ℝ Corr by rfl)).mp hker
  refine ⟨ContinuousLinearEquiv.ofBijective D hker hrange, ?_⟩
  exact ContinuousLinearEquiv.coe_ofBijective D hker hrange


end LogConcaveExtremum.CompactMomentMap

/-! ## Flattened source: `lean_ii/LocalDomain.lean` -/


open Filter Set
open scoped Topology

namespace CompactOnePiece

/-- A constraint that already holds throughout a neighborhood of the base
point can be removed from the set in a local maximum statement. -/
theorem isLocalMaxOn_of_inter_mem_nhds
    {E : Type*} [TopologicalSpace E]
    {φ : E → ℝ} {D S : Set E} {x₀ : E}
    (hD : D ∈ 𝓝 x₀) (hmax : IsLocalMaxOn φ (D ∩ S) x₀) :
    IsLocalMaxOn φ S x₀ := by
  unfold IsLocalMaxOn at hmax ⊢
  rwa [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hD)] at hmax

end CompactOnePiece

/-! ## Flattened source: `lean_ii/CurvatureThreshold.lean` -/


open Set

namespace CompactOnePiece

/-- The dimensionless profile controlling the sign of the residual curvature. -/
noncomputable def curvatureProfile (s : ℝ) : ℝ := (1 - s) * Real.exp (-s)

lemma curvatureProfile_zero : curvatureProfile 0 = 1 := by
  simp [curvatureProfile]

lemma curvatureProfile_one : curvatureProfile 1 = 0 := by
  simp [curvatureProfile]

lemma curvatureProfile_continuous : Continuous curvatureProfile := by
  unfold curvatureProfile
  fun_prop

lemma hasDerivAt_curvatureProfile (s : ℝ) :
    HasDerivAt curvatureProfile ((s - 2) * Real.exp (-s)) s := by
  have h := ((hasDerivAt_const s 1).sub (hasDerivAt_id s)).mul
    ((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_neg s))
  have h' := h.congr_deriv (show
      (0 - 1) * Real.exp (-s) + (1 - s) * (Real.exp (-s) * -1) =
        (s - 2) * Real.exp (-s) by ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with x
  simp [curvatureProfile, Function.comp_apply]

lemma curvatureProfile_strictAntiOn :
    StrictAntiOn curvatureProfile (Icc 0 1) := by
  intro x hx y hy hxy
  obtain ⟨z, hz, hz_slope⟩ :=
    exists_hasDerivAt_eq_slope curvatureProfile
      (fun s ↦ (s - 2) * Real.exp (-s)) hxy
      curvatureProfile_continuous.continuousOn
      (fun s _ ↦ hasDerivAt_curvatureProfile s)
  have hzlt : z < 2 := by linarith [hz.2, hy.2]
  have hderiv_neg : (z - 2) * Real.exp (-z) < 0 :=
    mul_neg_of_neg_of_pos (sub_neg.mpr hzlt) (Real.exp_pos _)
  rw [hz_slope] at hderiv_neg
  have hden : 0 < y - x := sub_pos.mpr hxy
  have := (div_lt_iff₀ hden).mp hderiv_neg
  linarith

/-- For `0 < gamma < 1`, the curvature profile crosses `gamma` exactly once
between zero and one.  Only existence and the order comparison are recorded. -/
theorem exists_curvatureProfile_threshold (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ s ∈ Ioo (0 : ℝ) 1,
      curvatureProfile s = γ ∧
      (∀ u ∈ Icc 0 1, u ≤ s → γ ≤ curvatureProfile u) ∧
      (∀ u ∈ Icc 0 1, s ≤ u → curvatureProfile u ≤ γ) := by
  have hmem : γ ∈ Ioo (curvatureProfile 1) (curvatureProfile 0) := by
    simpa [curvatureProfile_zero, curvatureProfile_one] using ⟨hγ0, hγ1⟩
  obtain ⟨s, hs, hsg⟩ :=
    (intermediate_value_Ioo' (show (0 : ℝ) ≤ 1 by norm_num)
      curvatureProfile_continuous.continuousOn) hmem
  refine ⟨s, hs, hsg, ?_, ?_⟩
  · intro u hu hus
    rcases hus.eq_or_lt with rfl | hus
    · exact hsg.ge
    · rw [← hsg]
      exact (curvatureProfile_strictAntiOn hu ⟨hs.1.le, hs.2.le⟩ hus).le
  · intro u hu hsu
    rcases hsu.eq_or_lt with rfl | hsu
    · exact hsg.le
    · rw [← hsg]
      exact (curvatureProfile_strictAntiOn ⟨hs.1.le, hs.2.le⟩ hu hsu).le

noncomputable def residualCurvature (α γ x : ℝ) : ℝ :=
  α ^ 2 * (γ + (α * |x| - 1) * Real.exp (-α * |x|))

/-- The residual curvature is nonpositive in one central interval and
nonnegative on the two complementary tails. -/
theorem exists_residualCurvature_threshold
    (α γ : ℝ) (hα : 0 < α) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ t, 0 < t ∧ t < 1 / α ∧
      (∀ x, |x| ≤ t → residualCurvature α γ x ≤ 0) ∧
      (∀ x, t ≤ |x| → 0 ≤ residualCurvature α γ x) ∧
      (∀ x, |x| < t → residualCurvature α γ x < 0) ∧
      (∀ x, t < |x| → 0 < residualCurvature α γ x) := by
  obtain ⟨s, hs, hsg, hbefore, hafter⟩ :=
    exists_curvatureProfile_threshold γ hγ0 hγ1
  refine ⟨s / α, div_pos hs.1 hα, (div_lt_div_iff_of_pos_right hα).2 ?_,
    ?_, ?_, ?_, ?_⟩
  · simpa using hs.2
  · intro x hx
    have hu0 : 0 ≤ α * |x| := mul_nonneg hα.le (abs_nonneg x)
    have hus : α * |x| ≤ s := by
      calc
        α * |x| ≤ α * (s / α) := mul_le_mul_of_nonneg_left hx hα.le
        _ = s := mul_div_cancel₀ s hα.ne'
    have hu1 : α * |x| ≤ 1 := hus.trans hs.2.le
    have hp := hbefore (α * |x|) ⟨hu0, hu1⟩ hus
    rw [curvatureProfile] at hp
    unfold residualCurvature
    have hinner : γ + (α * |x| - 1) * Real.exp (-α * |x|) ≤ 0 := by
      rw [show -α * |x| = -(α * |x|) by ring]
      nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg α) hinner
  · intro x hx
    have hsu : s ≤ α * |x| := by
      calc
        s = α * (s / α) := (mul_div_cancel₀ s hα.ne').symm
        _ ≤ α * |x| := mul_le_mul_of_nonneg_left hx hα.le
    by_cases hu1 : α * |x| ≤ 1
    · have hu0 : 0 ≤ α * |x| := mul_nonneg hα.le (abs_nonneg x)
      have hp := hafter (α * |x|) ⟨hu0, hu1⟩ hsu
      rw [curvatureProfile] at hp
      unfold residualCurvature
      have hinner : 0 ≤ γ + (α * |x| - 1) * Real.exp (-α * |x|) := by
        rw [show -α * |x| = -(α * |x|) by ring]
        nlinarith
      exact mul_nonneg (sq_nonneg α) hinner
    · have hterm : 0 ≤ (α * |x| - 1) * Real.exp (-α * |x|) :=
        mul_nonneg (sub_nonneg.mpr (le_of_not_ge hu1)) (Real.exp_pos _).le
      unfold residualCurvature
      exact mul_nonneg (sq_nonneg α) (add_nonneg hγ0.le hterm)
  · intro x hx
    have hu0 : 0 ≤ α * |x| := mul_nonneg hα.le (abs_nonneg x)
    have hus : α * |x| < s := by
      calc
        α * |x| < α * (s / α) := mul_lt_mul_of_pos_left hx hα
        _ = s := mul_div_cancel₀ s hα.ne'
    have hu1 : α * |x| ≤ 1 := (le_of_lt hus).trans hs.2.le
    have hp : γ < curvatureProfile (α * |x|) := by
      rw [← hsg]
      exact curvatureProfile_strictAntiOn ⟨hu0, hu1⟩ ⟨hs.1.le, hs.2.le⟩ hus
    rw [curvatureProfile] at hp
    unfold residualCurvature
    have hα2 : 0 < α ^ 2 := sq_pos_of_pos hα
    have hinner : γ + (α * |x| - 1) * Real.exp (-α * |x|) < 0 := by
      rw [show -α * |x| = -(α * |x|) by ring]
      nlinarith
    exact mul_neg_of_pos_of_neg hα2 hinner
  · intro x hx
    have hsu : s < α * |x| := by
      calc
        s = α * (s / α) := (mul_div_cancel₀ s hα.ne').symm
        _ < α * |x| := mul_lt_mul_of_pos_left hx hα
    by_cases hu1 : α * |x| ≤ 1
    · have hu0 : 0 ≤ α * |x| := mul_nonneg hα.le (abs_nonneg x)
      have hp : curvatureProfile (α * |x|) < γ := by
        rw [← hsg]
        exact curvatureProfile_strictAntiOn ⟨hs.1.le, hs.2.le⟩ ⟨hu0, hu1⟩ hsu
      rw [curvatureProfile] at hp
      unfold residualCurvature
      have hα2 : 0 < α ^ 2 := sq_pos_of_pos hα
      have hinner : 0 < γ + (α * |x| - 1) * Real.exp (-α * |x|) := by
        rw [show -α * |x| = -(α * |x|) by ring]
        nlinarith
      exact mul_pos hα2 hinner
    · have hterm : 0 ≤ (α * |x| - 1) * Real.exp (-α * |x|) :=
        mul_nonneg (sub_nonneg.mpr (le_of_not_ge hu1)) (Real.exp_pos _).le
      unfold residualCurvature
      have hα2 : 0 < α ^ 2 := sq_pos_of_pos hα
      exact mul_pos hα2 (add_pos_of_pos_of_nonneg hγ0 hterm)

end CompactOnePiece

/-! ## Flattened source: `lean_ii/ResidualShape.lean` -/


open Set

namespace CompactOnePiece

private theorem monotoneOn_Iic_of_hasDerivAt_nonneg
    {f f' : ℝ → ℝ} {a : ℝ}
    (hf : Continuous f)
    (hderiv : ∀ x < a, HasDerivAt f (f' x) x)
    (hsign : ∀ x < a, 0 ≤ f' x) :
    MonotoneOn f (Iic a) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  obtain ⟨z, hz, hz_slope⟩ :=
    exists_hasDerivAt_eq_slope f f' hxy hf.continuousOn
      (fun u hu ↦ hderiv u (hu.2.trans_le hy))
  have hs := hsign z (hz.2.trans_le hy)
  rw [hz_slope] at hs
  have hn : 0 ≤ f y - f x := by
    have := (le_div_iff₀ (sub_pos.mpr hxy)).mp hs
    simpa using this
  linarith

private theorem monotoneOn_Ici_of_hasDerivAt_nonneg
    {f f' : ℝ → ℝ} {a : ℝ}
    (hf : Continuous f)
    (hderiv : ∀ x, a < x → HasDerivAt f (f' x) x)
    (hsign : ∀ x, a < x → 0 ≤ f' x) :
    MonotoneOn f (Ici a) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  obtain ⟨z, hz, hz_slope⟩ :=
    exists_hasDerivAt_eq_slope f f' hxy hf.continuousOn
      (fun u hu ↦ hderiv u (hx.trans_lt hu.1))
  have hs := hsign z (hx.trans_lt hz.1)
  rw [hz_slope] at hs
  have hn : 0 ≤ f y - f x := by
    have := (le_div_iff₀ (sub_pos.mpr hxy)).mp hs
    simpa using this
  linarith

private theorem antitoneOn_Icc_of_hasDerivAt_nonpos
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f)
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hsign : ∀ x ∈ Ioo a b, f' x ≤ 0) :
    AntitoneOn f (Icc a b) := by
  intro x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hxy
  · exact le_rfl
  obtain ⟨z, hz, hz_slope⟩ :=
    exists_hasDerivAt_eq_slope f f' hxy hf.continuousOn
      (fun u hu ↦ hderiv u ⟨hx.1.trans_lt hu.1, hu.2.trans_le hy.2⟩)
  have hs := hsign z ⟨hx.1.trans_lt hz.1, hz.2.trans_le hy.2⟩
  rw [hz_slope] at hs
  have hn : f y - f x ≤ 0 := by
    have := (div_le_iff₀ (sub_pos.mpr hxy)).mp hs
    simpa using this
  linarith

noncomputable def residualSlope (α γ ell x : ℝ) : ℝ :=
  α ^ 2 * x * (γ - Real.exp (-α * |x|)) - ell

lemma residualSlope_continuous (α γ ell : ℝ) :
    Continuous (residualSlope α γ ell) := by
  unfold residualSlope
  fun_prop

lemma hasDerivAt_residualSlope_of_pos
    (α γ ell : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (residualSlope α γ ell) (residualCurvature α γ x) x := by
  have hlin := (hasDerivAt_id x).const_mul (-α)
  have he := (Real.hasDerivAt_exp (-α * x)).comp x hlin
  have hq := (hasDerivAt_const x γ).sub he
  have hp := (((hasDerivAt_const x (α ^ 2)).mul (hasDerivAt_id x)).mul hq).sub_const ell
  have hp' := hp.congr_deriv (show _ = residualCurvature α γ x by
    unfold residualCurvature
    rw [abs_of_pos hx]
    simp [Function.comp_apply]
    ring)
  apply hp'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  have hypos : 0 < y := hy
  simp [residualSlope, Function.comp_apply, abs_of_pos hypos]

lemma hasDerivAt_residualSlope_of_neg
    (α γ ell : ℝ) {x : ℝ} (hx : x < 0) :
    HasDerivAt (residualSlope α γ ell) (residualCurvature α γ x) x := by
  have hlin := (hasDerivAt_id x).const_mul α
  have he := (Real.hasDerivAt_exp (α * x)).comp x hlin
  have hq := (hasDerivAt_const x γ).sub he
  have hp := (((hasDerivAt_const x (α ^ 2)).mul (hasDerivAt_id x)).mul hq).sub_const ell
  have hp' := hp.congr_deriv (show _ = residualCurvature α γ x by
    unfold residualCurvature
    rw [abs_of_neg hx]
    simp [Function.comp_apply]
    ring)
  apply hp'.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hx] with y hy
  have hyneg : y < 0 := hy
  simp [residualSlope, Function.comp_apply, abs_of_neg hyneg]

/-- The derivative of a compact one-piece residual has the required
increasing--decreasing--increasing shape. -/
theorem residualSlope_three_shape
    (α γ ell : ℝ) (hα : 0 < α) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ t, 0 < t ∧
      MonotoneOn (residualSlope α γ ell) (Iic (-t)) ∧
      AntitoneOn (residualSlope α γ ell) (Icc (-t) t) ∧
      MonotoneOn (residualSlope α γ ell) (Ici t) := by
  obtain ⟨t, ht0, _ht1, hcentral, htails, _hcentral_strict, _htails_strict⟩ :=
    exists_residualCurvature_threshold α γ hα hγ0 hγ1
  refine ⟨t, ht0, ?_, ?_, ?_⟩
  · apply monotoneOn_Iic_of_hasDerivAt_nonneg (residualSlope_continuous α γ ell)
    · intro x hx
      exact hasDerivAt_residualSlope_of_neg α γ ell
        (hx.trans (neg_lt_zero.mpr ht0))
    · intro x hx
      have hxneg : x < 0 := hx.trans (neg_lt_zero.mpr ht0)
      apply htails x
      rw [abs_of_neg hxneg]
      simpa using neg_le_neg hx.le
  · have hneg : AntitoneOn (residualSlope α γ ell) (Icc (-t) 0) := by
      apply antitoneOn_Icc_of_hasDerivAt_nonpos (residualSlope_continuous α γ ell)
      · intro x hx
        exact hasDerivAt_residualSlope_of_neg α γ ell hx.2
      · intro x hx
        apply hcentral x
        rw [abs_of_neg hx.2]
        simpa using neg_le_neg hx.1.le
    have hpos : AntitoneOn (residualSlope α γ ell) (Icc 0 t) := by
      apply antitoneOn_Icc_of_hasDerivAt_nonpos (residualSlope_continuous α γ ell)
      · intro x hx
        exact hasDerivAt_residualSlope_of_pos α γ ell hx.1
      · intro x hx
        apply hcentral x
        simpa [abs_of_pos hx.1] using hx.2.le
    intro x hx y hy hxy
    by_cases hy0 : y ≤ 0
    · exact hneg ⟨hx.1, hxy.trans hy0⟩ ⟨le_trans hx.1 hxy, hy0⟩ hxy
    by_cases hx0 : 0 ≤ x
    · exact hpos ⟨hx0, hxy.trans hy.2⟩ ⟨le_of_not_ge hy0, hy.2⟩ hxy
    · exact (hpos ⟨le_rfl, ht0.le⟩ ⟨le_of_not_ge hy0, hy.2⟩
          (le_of_not_ge hy0)).trans
        (hneg ⟨hx.1, le_of_not_ge hx0⟩ ⟨neg_nonpos.mpr ht0.le, le_rfl⟩
          (le_of_not_ge hx0))
  · apply monotoneOn_Ici_of_hasDerivAt_nonneg (residualSlope_continuous α γ ell)
    · intro x hx
      exact hasDerivAt_residualSlope_of_pos α γ ell (ht0.trans hx)
    · intro x hx
      have hxpos : 0 < x := ht0.trans hx
      apply htails x
      simpa [abs_of_pos hxpos] using hx.le

end CompactOnePiece

/-! ## Flattened source: `lean_ii/Residual.lean` -/


open Set

namespace CompactOnePiece

noncomputable def gIntegrand (α x : ℝ) : ℝ := x * Real.exp (-α * |x|)

lemma gIntegrand_continuous (α : ℝ) : Continuous (gIntegrand α) := by
  unfold gIntegrand
  fun_prop

/-- A globally smooth presentation of `(1+α|x|) exp (-α|x|)`.
The equality with that elementary expression is recorded below. -/
noncomputable def smoothG (α x : ℝ) : ℝ :=
  1 - α ^ 2 * ∫ t in 0..x, gIntegrand α t

lemma hasDerivAt_smoothG (α x : ℝ) :
    HasDerivAt (smoothG α) (-α ^ 2 * x * Real.exp (-α * |x|)) x := by
  have hi : HasDerivAt (fun y : ℝ ↦ ∫ t in 0..y, gIntegrand α t)
      (gIntegrand α x) x :=
    ((gIntegrand_continuous α).integral_hasStrictDerivAt 0 x).hasDerivAt
  have h := (hasDerivAt_const x 1).sub
    ((hasDerivAt_const x (α ^ 2)).mul hi)
  have h' := h.congr_deriv (show
      0 - (0 * (∫ t in 0..x, gIntegrand α t) + α ^ 2 * gIntegrand α x) =
        -α ^ 2 * x * Real.exp (-α * |x|) by
    unfold gIntegrand
    ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [smoothG]

lemma smoothG_continuous (α : ℝ) : Continuous (smoothG α) := by
  rw [continuous_iff_continuousAt]
  exact fun x ↦ (hasDerivAt_smoothG α x).continuousAt

noncomputable def residual (α l0 l1 l2 x : ℝ) : ℝ :=
  smoothG α x - l0 - l1 * x - l2 * x ^ 2

lemma residual_continuous (α l0 l1 l2 : ℝ) :
    Continuous (residual α l0 l1 l2) := by
  unfold residual
  exact (((smoothG_continuous α).sub continuous_const).sub
    (continuous_const.mul continuous_id)).sub
      (continuous_const.mul (continuous_id.pow 2))

lemma hasDerivAt_residual (α l0 l1 l2 x : ℝ) :
    HasDerivAt (residual α l0 l1 l2)
      (-α ^ 2 * x * Real.exp (-α * |x|) - l1 - 2 * l2 * x) x := by
  have h := (((hasDerivAt_smoothG α x).sub_const l0).sub
      ((hasDerivAt_const x l1).mul (hasDerivAt_id x))).sub
        ((hasDerivAt_const x l2).mul ((hasDerivAt_id x).pow 2))
  have h' := h.congr_deriv (show
      -α ^ 2 * x * Real.exp (-α * |x|) -
          (0 * id x + l1 * 1) -
          (0 * (id ^ 2) x + l2 * ((2 : ℝ) * id x ^ (2 - 1) * 1)) =
        -α ^ 2 * x * Real.exp (-α * |x|) - l1 - 2 * l2 * x by
    simp
    ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [residual]

lemma hasDerivAt_residual_of_multiplier_identity
    (α γ l0 l1 l2 x : ℝ) (hl2 : 2 * l2 = -α ^ 2 * γ) :
    HasDerivAt (residual α l0 l1 l2) (residualSlope α γ l1 x) x := by
  convert hasDerivAt_residual α l0 l1 l2 x using 1
  unfold residualSlope
  linear_combination x * hl2

end CompactOnePiece

/-! ## Flattened source: `lean_ii/ThreeShape.lean` -/


/-!
An elementary calculus lemma used in the compact one-piece case.

If the derivative of a function is increasing, then decreasing, then increasing,
and its endpoint derivatives point into the interval, a function which vanishes
at both endpoints cannot be negative between them.
-/

open Set

namespace CompactOnePiece

theorem nonneg_of_derivative_three_shape
    {r r' : ℝ → ℝ} {A B t : ℝ}
    (hAB : A < B)
    (hr_cont : Continuous r)
    (hr_deriv : ∀ x, HasDerivAt r (r' x) x)
    (hrA : r A = 0) (hrB : r B = 0)
    (hrA' : 0 ≤ r' A) (hrB' : r' B ≤ 0)
    (hleft : MonotoneOn r' (Iic (-t)))
    (hmiddle : AntitoneOn r' (Icc (-t) t))
    (hright : MonotoneOn r' (Ici t)) :
    ∀ x ∈ Icc A B, 0 ≤ r x := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hAx
  · simp [hrA]
  rcases eq_or_lt_of_le hx.2 with rfl | hxB
  · simp [hrB]
  by_contra hneg
  have hrx : r x < 0 := lt_of_not_ge hneg
  obtain ⟨u, hu, hu_slope⟩ :=
    exists_hasDerivAt_eq_slope r r' hAx hr_cont.continuousOn
      (fun y _ ↦ hr_deriv y)
  obtain ⟨v, hv, hv_slope⟩ :=
    exists_hasDerivAt_eq_slope r r' hxB hr_cont.continuousOn
      (fun y _ ↦ hr_deriv y)
  have hu_neg : r' u < 0 := by
    rw [hu_slope, hrA]
    exact div_neg_of_neg_of_pos (by simpa using hrx) (sub_pos.mpr hAx)
  have hv_pos : 0 < r' v := by
    rw [hv_slope, hrB]
    exact div_pos (by simpa using neg_pos.mpr hrx) (sub_pos.mpr hxB)
  have hut : -t < u := by
    by_contra h
    have hu_le : u ≤ -t := le_of_not_gt h
    have hA_le : A ≤ -t := (le_of_lt hu.1).trans hu_le
    have := hleft hA_le hu_le (le_of_lt hu.1)
    linarith
  have hvt : v < t := by
    by_contra h
    have ht_le : t ≤ v := le_of_not_gt h
    have htB : t ≤ B := ht_le.trans (le_of_lt hv.2)
    have := hright ht_le htB (le_of_lt hv.2)
    linarith
  have huv : u ≤ v := by linarith [hu.2, hv.1]
  have hu_mid : u ∈ Icc (-t) t := ⟨le_of_lt hut, by linarith⟩
  have hv_mid : v ∈ Icc (-t) t := ⟨by linarith, le_of_lt hvt⟩
  have := hmiddle hu_mid hv_mid huv
  linarith

/-- The preceding shape is incompatible with a zero weighted integral unless
the residual vanishes identically on the support. -/
theorem integral_ne_zero_of_derivative_three_shape
    {r r' w : ℝ → ℝ} {A B t : ℝ}
    (hAB : A < B)
    (hr_cont : Continuous r) (hw_cont : Continuous w)
    (hw_pos : ∀ x, 0 < w x)
    (hr_deriv : ∀ x, HasDerivAt r (r' x) x)
    (hrA : r A = 0) (hrB : r B = 0)
    (hrA' : 0 ≤ r' A) (hrB' : r' B ≤ 0)
    (hleft : MonotoneOn r' (Iic (-t)))
    (hmiddle : AntitoneOn r' (Icc (-t) t))
    (hright : MonotoneOn r' (Ici t))
    (hnonzero : ∃ x ∈ Icc A B, r x ≠ 0) :
    0 < ∫ x in A..B, r x * w x := by
  have hr_nonneg := nonneg_of_derivative_three_shape hAB hr_cont hr_deriv
    hrA hrB hrA' hrB' hleft hmiddle hright
  apply intervalIntegral.integral_pos hAB (hr_cont.mul hw_cont).continuousOn
  · intro x hx
    exact mul_nonneg (hr_nonneg x ⟨hx.1.le, hx.2⟩) (hw_pos x).le
  · obtain ⟨x, hx, hx0⟩ := hnonzero
    refine ⟨x, hx, mul_pos ?_ (hw_pos x)⟩
    exact lt_of_le_of_ne (hr_nonneg x hx) (Ne.symm hx0)

theorem no_zero_integral_of_derivative_three_shape
    {r r' w : ℝ → ℝ} {A B t : ℝ}
    (hAB : A < B)
    (hr_cont : Continuous r) (hw_cont : Continuous w)
    (hw_pos : ∀ x, 0 < w x)
    (hr_deriv : ∀ x, HasDerivAt r (r' x) x)
    (hrA : r A = 0) (hrB : r B = 0)
    (hrA' : 0 ≤ r' A) (hrB' : r' B ≤ 0)
    (hleft : MonotoneOn r' (Iic (-t)))
    (hmiddle : AntitoneOn r' (Icc (-t) t))
    (hright : MonotoneOn r' (Ici t))
    (hnonzero : ∃ x ∈ Icc A B, r x ≠ 0)
    (hzero : (∫ x in A..B, r x * w x) = 0) : False := by
  have hpos := integral_ne_zero_of_derivative_three_shape hAB hr_cont hw_cont hw_pos
    hr_deriv hrA hrB hrA' hrB' hleft hmiddle hright hnonzero
  linarith

end CompactOnePiece

/-! ## Flattened source: `lean_ii/EndpointSlope.lean` -/


open Set

namespace CompactOnePiece

private lemma local_neg_of_continuous_of_neg
    {f : ℝ → ℝ} {a : ℝ} (hf : Continuous f) (ha : f a < 0) :
    ∃ δ > 0, ∀ x, |x - a| < δ → f x < 0 := by
  have hc : ContinuousAt f a := hf.continuousAt
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hclose⟩ := hc (-f a) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hd : dist x a < δ := by simpa [Real.dist_eq] using hx
  have hh := hclose hd
  rw [Real.dist_eq] at hh
  have := (abs_lt.mp hh).2
  linarith

private lemma local_pos_of_continuous_of_pos
    {f : ℝ → ℝ} {a : ℝ} (hf : Continuous f) (ha : 0 < f a) :
    ∃ δ > 0, ∀ x, |x - a| < δ → 0 < f x := by
  have hc : ContinuousAt f a := hf.continuousAt
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hclose⟩ := hc (f a) ha
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hd : dist x a < δ := by simpa [Real.dist_eq] using hx
  have hh := hclose hd
  rw [Real.dist_eq] at hh
  have := (abs_lt.mp hh).1
  linarith

/-- A nonnegative function with a third-order zero at the left endpoint has
nonnegative third derivative there.  This is the abstract endpoint argument
used for the hinge functional `Q`. -/
theorem third_derivative_nonneg_at_left
    {Q Q₁ Q₂ Q₃ : ℝ → ℝ} {A B : ℝ}
    (hAB : A < B)
    (hQ_nonneg : ∀ x ∈ Icc A B, 0 ≤ Q x)
    (hQ0 : Q A = 0) (hQ1 : Q₁ A = 0) (hQ2 : Q₂ A = 0)
    (hderiv0 : ∀ x, HasDerivAt Q (Q₁ x) x)
    (hderiv1 : ∀ x, HasDerivAt Q₁ (Q₂ x) x)
    (hderiv2 : ∀ x, HasDerivAt Q₂ (Q₃ x) x)
    (hQ3_cont : Continuous Q₃) :
    0 ≤ Q₃ A := by
  by_contra h
  have hneg : Q₃ A < 0 := lt_of_not_ge h
  obtain ⟨δ, hδ, hlocal⟩ := local_neg_of_continuous_of_neg hQ3_cont hneg
  let d := min δ ((B - A) / 2)
  have hd : 0 < d := lt_min hδ (by linarith)
  let b := A + d
  have hAb : A < b := by dsimp [b]; linarith
  have hbB : b < B := by
    dsimp [b, d]
    have hle : min δ ((B - A) / 2) ≤ (B - A) / 2 := min_le_right _ _
    linarith
  have hQ_cont : Continuous Q :=
    continuous_iff_continuousAt.mpr (fun x ↦ (hderiv0 x).continuousAt)
  have hQ1_cont : Continuous Q₁ :=
    continuous_iff_continuousAt.mpr (fun x ↦ (hderiv1 x).continuousAt)
  have hQ2_cont : Continuous Q₂ :=
    continuous_iff_continuousAt.mpr (fun x ↦ (hderiv2 x).continuousAt)
  obtain ⟨u, hu, hu_slope⟩ :=
    exists_hasDerivAt_eq_slope Q Q₁ hAb
      hQ_cont.continuousOn
      (fun x _ ↦ hderiv0 x)
  obtain ⟨v, hv, hv_slope⟩ :=
    exists_hasDerivAt_eq_slope Q₁ Q₂ hu.1
      hQ1_cont.continuousOn
      (fun x _ ↦ hderiv1 x)
  obtain ⟨w, hw, hw_slope⟩ :=
    exists_hasDerivAt_eq_slope Q₂ Q₃ hv.1
      hQ2_cont.continuousOn
      (fun x _ ↦ hderiv2 x)
  have hQb : 0 ≤ Q b := hQ_nonneg b ⟨hAb.le, hbB.le⟩
  have hQ1u : 0 ≤ Q₁ u := by
    rw [hu_slope, hQ0]
    exact div_nonneg (by simpa using hQb) (sub_nonneg.mpr hAb.le)
  have hQ2v : 0 ≤ Q₂ v := by
    rw [hv_slope, hQ1]
    exact div_nonneg (by simpa using hQ1u) (sub_nonneg.mpr hu.1.le)
  have hQ3w : 0 ≤ Q₃ w := by
    rw [hw_slope, hQ2]
    exact div_nonneg (by simpa using hQ2v) (sub_nonneg.mpr hv.1.le)
  have hwd : |w - A| < δ := by
    have hwb : w < b := hw.2.trans (hv.2.trans hu.2)
    have hw_lt_d : w - A < d := by
      dsimp [b] at hwb
      linarith
    have hdδ : d ≤ δ := min_le_left _ _
    rw [abs_of_pos (sub_pos.mpr hw.1)]
    exact hw_lt_d.trans_le hdδ
  linarith [hlocal w hwd]

/-- Right-endpoint counterpart of `third_derivative_nonneg_at_left`. -/
theorem third_derivative_nonpos_at_right
    {Q Q₁ Q₂ Q₃ : ℝ → ℝ} {A B : ℝ}
    (hAB : A < B)
    (hQ_nonneg : ∀ x ∈ Icc A B, 0 ≤ Q x)
    (hQ0 : Q B = 0) (hQ1 : Q₁ B = 0) (hQ2 : Q₂ B = 0)
    (hderiv0 : ∀ x, HasDerivAt Q (Q₁ x) x)
    (hderiv1 : ∀ x, HasDerivAt Q₁ (Q₂ x) x)
    (hderiv2 : ∀ x, HasDerivAt Q₂ (Q₃ x) x)
    (hQ3_cont : Continuous Q₃) :
    Q₃ B ≤ 0 := by
  by_contra h
  have hpos : 0 < Q₃ B := lt_of_not_ge h
  obtain ⟨δ, hδ, hlocal⟩ := local_pos_of_continuous_of_pos hQ3_cont hpos
  let d := min δ ((B - A) / 2)
  have hd : 0 < d := lt_min hδ (by linarith)
  let a := B - d
  have haB : a < B := by dsimp [a]; linarith
  have hAa : A < a := by
    dsimp [a, d]
    have hle : min δ ((B - A) / 2) ≤ (B - A) / 2 := min_le_right _ _
    linarith
  have hQ_cont : Continuous Q :=
    continuous_iff_continuousAt.mpr (fun x ↦ (hderiv0 x).continuousAt)
  have hQ1_cont : Continuous Q₁ :=
    continuous_iff_continuousAt.mpr (fun x ↦ (hderiv1 x).continuousAt)
  have hQ2_cont : Continuous Q₂ :=
    continuous_iff_continuousAt.mpr (fun x ↦ (hderiv2 x).continuousAt)
  obtain ⟨u, hu, hu_slope⟩ :=
    exists_hasDerivAt_eq_slope Q Q₁ haB
      hQ_cont.continuousOn
      (fun x _ ↦ hderiv0 x)
  obtain ⟨v, hv, hv_slope⟩ :=
    exists_hasDerivAt_eq_slope Q₁ Q₂ hu.2
      hQ1_cont.continuousOn
      (fun x _ ↦ hderiv1 x)
  obtain ⟨w, hw, hw_slope⟩ :=
    exists_hasDerivAt_eq_slope Q₂ Q₃ hv.2
      hQ2_cont.continuousOn
      (fun x _ ↦ hderiv2 x)
  have hQa : 0 ≤ Q a := hQ_nonneg a ⟨hAa.le, haB.le⟩
  have hQ1u : Q₁ u ≤ 0 := by
    rw [hu_slope, hQ0]
    exact div_nonpos_of_nonpos_of_nonneg (by simpa using neg_nonpos.mpr hQa)
      (sub_nonneg.mpr haB.le)
  have hQ2v : 0 ≤ Q₂ v := by
    rw [hv_slope, hQ1]
    exact div_nonneg (by simpa using neg_nonneg.mpr hQ1u) (sub_nonneg.mpr hu.2.le)
  have hQ3w : Q₃ w ≤ 0 := by
    rw [hw_slope, hQ2]
    exact div_nonpos_of_nonpos_of_nonneg (by simpa using neg_nonpos.mpr hQ2v)
      (sub_nonneg.mpr hv.2.le)
  have hwd : |w - B| < δ := by
    have haw : a < w := hu.1.trans (hv.1.trans hw.1)
    have hd_lt : B - w < d := by
      dsimp [a] at haw
      linarith
    have hdδ : d ≤ δ := min_le_left _ _
    rw [abs_of_neg (sub_neg.mpr hw.2)]
    simp only [neg_sub]
    exact hd_lt.trans_le hdδ
  linarith [hlocal w hwd]

end CompactOnePiece

/-! ## Flattened source: `lean_ii/HingeQ.lean` -/


open Set

namespace CompactOnePiece

noncomputable def primitive (R : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in 0..x, R y

noncomputable def momentPrimitive (R : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in 0..x, y * R y

noncomputable def tailIntegral (R : ℝ → ℝ) (B s : ℝ) : ℝ := primitive R B - primitive R s

noncomputable def tailMoment (R : ℝ → ℝ) (B s : ℝ) : ℝ :=
  momentPrimitive R B - momentPrimitive R s

/-- Algebraic form of `∫_s^B (x-s)R(x) dx`. -/
noncomputable def hingeQ (R : ℝ → ℝ) (B s : ℝ) : ℝ :=
  tailMoment R B s - s * tailIntegral R B s

lemma tailIntegral_eq_intervalIntegral
    {R : ℝ → ℝ} (hR : Continuous R) (B A : ℝ) :
    tailIntegral R B A = ∫ x in A..B, R x := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hR.intervalIntegrable (μ := MeasureTheory.volume) 0 A)
    (hR.intervalIntegrable (μ := MeasureTheory.volume) A B)
  unfold tailIntegral primitive
  linarith

lemma tailMoment_eq_intervalIntegral
    {R : ℝ → ℝ} (hR : Continuous R) (B A : ℝ) :
    tailMoment R B A = ∫ x in A..B, x * R x := by
  have hcont : Continuous (fun x : ℝ ↦ x * R x) := continuous_id.mul hR
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 A)
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) A B)
  unfold tailMoment momentPrimitive
  linarith

lemma hingeQ_eq_intervalIntegral
    {R : ℝ → ℝ} (hR : Continuous R) (B s : ℝ) :
    hingeQ R B s = ∫ x in s..B, (x - s) * R x := by
  have hRI : IntervalIntegrable R MeasureTheory.volume s B :=
    hR.intervalIntegrable (μ := MeasureTheory.volume) s B
  have hxRI : IntervalIntegrable (fun x : ℝ ↦ x * R x)
      MeasureTheory.volume s B := by
    apply ((continuous_id.mul hR).intervalIntegrable
      (μ := MeasureTheory.volume) s B).congr
    intro x _
    rfl
  rw [hingeQ, tailMoment_eq_intervalIntegral hR,
    tailIntegral_eq_intervalIntegral hR,
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub hxRI (hRI.const_mul s)]
  apply intervalIntegral.integral_congr
  intro x _
  ring

/-- The full-support hinge integral used by the variational calculation is
the same as `hingeQ` when the hinge point lies in the support. -/
lemma integral_max_sub_eq_hingeQ
    {R : ℝ → ℝ} (hR : Continuous R) {A B s : ℝ} (hs : s ∈ Icc A B) :
    (∫ x in A..B, max (x - s) 0 * R x) = hingeQ R B s := by
  have hH : Continuous (fun x : ℝ ↦ max (x - s) 0 * R x) := by
    fun_prop
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hH.intervalIntegrable (μ := MeasureTheory.volume) A s)
    (hH.intervalIntegrable (μ := MeasureTheory.volume) s B)
  have hleft : (∫ x in A..s, max (x - s) 0 * R x) = 0 := by
    calc
      (∫ x in A..s, max (x - s) 0 * R x) = ∫ _x in A..s, 0 := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Icc A s := by simpa [uIcc_of_le hs.1] using hx
        change max (x - s) 0 * R x = 0
        rw [max_eq_right (sub_nonpos.mpr hx'.2)]
        simp
      _ = 0 := by simp
  have hright : (∫ x in s..B, max (x - s) 0 * R x) =
      ∫ x in s..B, (x - s) * R x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc s B := by simpa [uIcc_of_le hs.2] using hx
    change max (x - s) 0 * R x = (x - s) * R x
    rw [max_eq_left (sub_nonneg.mpr hx'.1)]
  calc
    (∫ x in A..B, max (x - s) 0 * R x) =
        (∫ x in A..s, max (x - s) 0 * R x) +
          ∫ x in s..B, max (x - s) 0 * R x := hadd.symm
    _ = ∫ x in s..B, (x - s) * R x := by rw [hleft, zero_add, hright]
    _ = hingeQ R B s := (hingeQ_eq_intervalIntegral hR B s).symm

lemma hasDerivAt_primitive {R : ℝ → ℝ} (hR : Continuous R) (x : ℝ) :
    HasDerivAt (primitive R) (R x) x := by
  exact (hR.integral_hasStrictDerivAt 0 x).hasDerivAt

lemma hasDerivAt_momentPrimitive {R : ℝ → ℝ} (hR : Continuous R) (x : ℝ) :
    HasDerivAt (momentPrimitive R) (x * R x) x := by
  exact ((continuous_id.mul hR).integral_hasStrictDerivAt 0 x).hasDerivAt

lemma hasDerivAt_tailIntegral {R : ℝ → ℝ} (hR : Continuous R) (B s : ℝ) :
    HasDerivAt (tailIntegral R B) (-R s) s := by
  have h := (hasDerivAt_const s (primitive R B)).sub (hasDerivAt_primitive hR s)
  have h' := h.congr_deriv (show 0 - R s = -R s by ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [tailIntegral]

lemma hasDerivAt_tailMoment {R : ℝ → ℝ} (hR : Continuous R) (B s : ℝ) :
    HasDerivAt (tailMoment R B) (-s * R s) s := by
  have h := (hasDerivAt_const s (momentPrimitive R B)).sub
    (hasDerivAt_momentPrimitive hR s)
  have h' := h.congr_deriv (show 0 - s * R s = -s * R s by ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [tailMoment]

lemma hasDerivAt_hingeQ {R : ℝ → ℝ} (hR : Continuous R) (B s : ℝ) :
    HasDerivAt (hingeQ R B) (-tailIntegral R B s) s := by
  have h := (hasDerivAt_tailMoment hR B s).sub
    ((hasDerivAt_id s).mul (hasDerivAt_tailIntegral hR B s))
  have h' := h.congr_deriv (show
      -s * R s - (1 * tailIntegral R B s + s * (-R s)) =
        -tailIntegral R B s by ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [hingeQ]

lemma hasDerivAt_neg_tailIntegral {R : ℝ → ℝ} (hR : Continuous R) (B s : ℝ) :
    HasDerivAt (fun u ↦ -tailIntegral R B u) (R s) s := by
  have h := (hasDerivAt_tailIntegral hR B s).neg
  exact h.congr_deriv (show -(-R s) = R s by ring)

@[simp] lemma tailIntegral_self (R : ℝ → ℝ) (B : ℝ) : tailIntegral R B B = 0 := by
  simp [tailIntegral]

@[simp] lemma tailMoment_self (R : ℝ → ℝ) (B : ℝ) : tailMoment R B B = 0 := by
  simp [tailMoment]

@[simp] lemma hingeQ_self (R : ℝ → ℝ) (B : ℝ) : hingeQ R B B = 0 := by
  simp [hingeQ]

/-- Endpoint signs extracted from the hinge inequality.  Moment stationarity is
encoded by the two left-endpoint identities for `tailIntegral` and
`tailMoment`; at the right endpoint they hold definitionally. -/
theorem endpoint_signs_of_hingeQ_nonneg
    {R R' : ℝ → ℝ} {A B : ℝ}
    (hAB : A < B)
    (hR : Continuous R) (hR' : Continuous R')
    (hderivR : ∀ x, HasDerivAt R (R' x) x)
    (hRA : R A = 0) (hRB : R B = 0)
    (htailA : tailIntegral R B A = 0)
    (hmomentA : tailMoment R B A = 0)
    (hQ : ∀ s ∈ Icc A B, 0 ≤ hingeQ R B s) :
    0 ≤ R' A ∧ R' B ≤ 0 := by
  have hQA : hingeQ R B A = 0 := by simp [hingeQ, htailA, hmomentA]
  have hQ1A : -tailIntegral R B A = 0 := by simp [htailA]
  have hleft := third_derivative_nonneg_at_left hAB hQ hQA hQ1A hRA
    (hasDerivAt_hingeQ hR B)
    (hasDerivAt_neg_tailIntegral hR B)
    hderivR hR'
  have hright := third_derivative_nonpos_at_right hAB hQ
    (hingeQ_self R B) (by simp) hRB
    (hasDerivAt_hingeQ hR B)
    (hasDerivAt_neg_tailIntegral hR B)
    hderivR hR'
  exact ⟨hleft, hright⟩

end CompactOnePiece

/-! ## Flattened source: `lean_ii/ClaimII.lean` -/


open Set

namespace CompactOnePiece

noncomputable def exponentialWeight (c β x : ℝ) : ℝ := Real.exp (c + β * x)

lemma exponentialWeight_continuous (c β : ℝ) :
    Continuous (exponentialWeight c β) := by
  unfold exponentialWeight
  fun_prop

lemma exponentialWeight_pos (c β x : ℝ) : 0 < exponentialWeight c β x := by
  exact Real.exp_pos _

/-- The residual cannot vanish identically on a nondegenerate interval.  The
proof only uses that its derivative is `residualSlope` and that the latter has
strictly nonzero derivative away from the three exceptional points
`0, -t, t`. -/
lemma exists_residual_ne_zero
    (α γ l0 l1 l2 A B : ℝ)
    (hα : 0 < α) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hAB : A < B) (hl2 : 2 * l2 = -α ^ 2 * γ) :
    ∃ x ∈ Icc A B, residual α l0 l1 l2 x ≠ 0 := by
  classical
  obtain ⟨t, ht0, _ht1, _hcentral, _htails, hcentral_strict, htails_strict⟩ :=
    exists_residualCurvature_threshold α γ hα hγ0 hγ1
  let S : Set ℝ := {0, t, -t}
  have hS : S.Finite := by
    simp [S]
  obtain ⟨x, hx, hxS⟩ := (Ioo_infinite hAB).exists_notMem_finite hS
  have hx0 : x ≠ 0 := by
    intro h
    apply hxS
    simp [S, h]
  have hxt : |x| ≠ t := by
    intro h
    apply hxS
    by_cases hxnonneg : 0 ≤ x
    · have hxeq : x = t := by simpa [abs_of_nonneg hxnonneg] using h
      simp [S, hxeq]
    · have hxneg : x < 0 := lt_of_not_ge hxnonneg
      have hxeq : x = -t := by
        rw [abs_of_neg hxneg] at h
        linarith
      simp [S, hxeq]
  by_contra hall
  push Not at hall
  have hslope_zero : ∀ y ∈ Ioo A B, residualSlope α γ l1 y = 0 := by
    intro y hy
    have heq : residual α l0 l1 l2 =ᶠ[nhds y] (fun _ : ℝ ↦ 0) := by
      filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
      exact hall z ⟨hz.1.le, hz.2.le⟩
    have hzero : HasDerivAt (residual α l0 l1 l2) 0 y :=
      (hasDerivAt_const y 0).congr_of_eventuallyEq heq
    exact (hasDerivAt_residual_of_multiplier_identity
      α γ l0 l1 l2 y hl2).unique hzero
  have heqSlope : residualSlope α γ l1 =ᶠ[nhds x] (fun _ : ℝ ↦ 0) := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact hslope_zero y hy
  have hzeroSlope : HasDerivAt (residualSlope α γ l1) 0 x :=
    (hasDerivAt_const x 0).congr_of_eventuallyEq heqSlope
  have hcurvDeriv :
      HasDerivAt (residualSlope α γ l1) (residualCurvature α γ x) x := by
    rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · exact hasDerivAt_residualSlope_of_neg α γ l1 hxneg
    · exact hasDerivAt_residualSlope_of_pos α γ l1 hxpos
  have hcurv0 : residualCurvature α γ x = 0 := hcurvDeriv.unique hzeroSlope
  rcases lt_or_gt_of_ne hxt with hlt | hgt
  · exact (ne_of_lt (hcentral_strict x hlt)) hcurv0
  · exact (ne_of_gt (htails_strict x hgt)) hcurv0

/-- Calculus core of Claim (ii).

The hypotheses are precisely the consequences of the KKT and hinge variations:
the multiplier identity, two endpoint values, two inward endpoint slopes, and
the zero residual integral.  The conclusion says that no nonzero residual can
satisfy all of them on a compact one-piece log-affine support. -/
theorem compact_onePiece_residual_impossible
    (α γ l0 l1 l2 c β A B : ℝ)
    (hα : 0 < α) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hAB : A < B)
    (hl2 : 2 * l2 = -α ^ 2 * γ)
    (hrA : residual α l0 l1 l2 A = 0)
    (hrB : residual α l0 l1 l2 B = 0)
    (hrA' : 0 ≤ residualSlope α γ l1 A)
    (hrB' : residualSlope α γ l1 B ≤ 0)
    (hzero :
      (∫ x in A..B,
        residual α l0 l1 l2 x * exponentialWeight c β x) = 0) : False := by
  obtain ⟨t, _ht, hleft, hmiddle, hright⟩ :=
    residualSlope_three_shape α γ l1 hα hγ0 hγ1
  exact no_zero_integral_of_derivative_three_shape hAB
    (residual_continuous α l0 l1 l2)
    (exponentialWeight_continuous c β)
    (exponentialWeight_pos c β)
    (hasDerivAt_residual_of_multiplier_identity α γ l0 l1 l2 · hl2)
    hrA hrB hrA' hrB' hleft hmiddle hright
    (exists_residual_ne_zero α γ l0 l1 l2 A B hα hγ0 hγ1 hAB hl2) hzero

noncomputable def weightedResidual
    (α l0 l1 l2 c β x : ℝ) : ℝ :=
  residual α l0 l1 l2 x * exponentialWeight c β x

noncomputable def weightedResidualDerivative
    (α γ l0 l1 l2 c β x : ℝ) : ℝ :=
  (residualSlope α γ l1 x + β * residual α l0 l1 l2 x) *
    exponentialWeight c β x

lemma hasDerivAt_exponentialWeight (c β x : ℝ) :
    HasDerivAt (exponentialWeight c β) (β * exponentialWeight c β x) x := by
  have h := (Real.hasDerivAt_exp (c + β * x)).comp x
    ((hasDerivAt_const x c).add ((hasDerivAt_const x β).mul (hasDerivAt_id x)))
  have h' := h.congr_deriv (show
      Real.exp (c + β * x) * (0 + (0 * x + β * 1)) =
        β * exponentialWeight c β x by
    simp [exponentialWeight]
    ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [exponentialWeight, Function.comp_apply]

lemma weightedResidual_continuous (α l0 l1 l2 c β : ℝ) :
  Continuous (weightedResidual α l0 l1 l2 c β) := by
  unfold weightedResidual
  exact (residual_continuous α l0 l1 l2).mul (exponentialWeight_continuous c β)

lemma weightedResidualDerivative_continuous (α γ l0 l1 l2 c β : ℝ) :
  Continuous (weightedResidualDerivative α γ l0 l1 l2 c β) := by
  unfold weightedResidualDerivative
  exact ((residualSlope_continuous α γ l1).add
    ((residual_continuous α l0 l1 l2).const_mul β)).mul
      (exponentialWeight_continuous c β)

lemma hasDerivAt_weightedResidual
    (α γ l0 l1 l2 c β x : ℝ)
    (hl2 : 2 * l2 = -α ^ 2 * γ) :
    HasDerivAt (weightedResidual α l0 l1 l2 c β)
      (weightedResidualDerivative α γ l0 l1 l2 c β x) x := by
  have h := (hasDerivAt_residual_of_multiplier_identity
    α γ l0 l1 l2 x hl2).mul (hasDerivAt_exponentialWeight c β x)
  have h' := h.congr_deriv (show
      residualSlope α γ l1 x * exponentialWeight c β x +
          residual α l0 l1 l2 x * (β * exponentialWeight c β x) =
        weightedResidualDerivative α γ l0 l1 l2 c β x by
    unfold weightedResidualDerivative
    ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [weightedResidual]

/-- Version of Claim (ii)'s calculus core whose endpoint slope hypotheses are
deduced from the hinge inequality `Q ≥ 0`. -/
theorem compact_onePiece_residual_impossible_of_hinge
    (α γ l0 l1 l2 c β A B : ℝ)
    (hα : 0 < α) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hAB : A < B)
    (hl2 : 2 * l2 = -α ^ 2 * γ)
    (hrA : residual α l0 l1 l2 A = 0)
    (hrB : residual α l0 l1 l2 B = 0)
    (htailA : tailIntegral (weightedResidual α l0 l1 l2 c β) B A = 0)
    (hmomentA : tailMoment (weightedResidual α l0 l1 l2 c β) B A = 0)
    (hQ : ∀ s ∈ Icc A B,
      0 ≤ hingeQ (weightedResidual α l0 l1 l2 c β) B s) : False := by
  have hRA : weightedResidual α l0 l1 l2 c β A = 0 := by
    simp [weightedResidual, hrA]
  have hRB : weightedResidual α l0 l1 l2 c β B = 0 := by
    simp [weightedResidual, hrB]
  obtain ⟨hleft, hright⟩ := endpoint_signs_of_hingeQ_nonneg hAB
    (weightedResidual_continuous α l0 l1 l2 c β)
    (weightedResidualDerivative_continuous α γ l0 l1 l2 c β)
    (fun x ↦ hasDerivAt_weightedResidual α γ l0 l1 l2 c β x hl2)
    hRA hRB htailA hmomentA hQ
  have hrA' : 0 ≤ residualSlope α γ l1 A := by
    unfold weightedResidualDerivative at hleft
    rw [hrA] at hleft
    simp only [mul_zero, add_zero] at hleft
    exact nonneg_of_mul_nonneg_left hleft (exponentialWeight_pos c β A)
  have hrB' : residualSlope α γ l1 B ≤ 0 := by
    unfold weightedResidualDerivative at hright
    rw [hrB] at hright
    simp only [mul_zero, add_zero] at hright
    exact nonpos_of_mul_nonpos_left hright (exponentialWeight_pos c β B)
  have hzero :
      (∫ x in A..B,
        residual α l0 l1 l2 x * exponentialWeight c β x) = 0 := by
    calc
      (∫ x in A..B, residual α l0 l1 l2 x * exponentialWeight c β x) =
          ∫ x in A..B, weightedResidual α l0 l1 l2 c β x := by
        apply intervalIntegral.integral_congr
        intro x _
        rfl
      _ = tailIntegral (weightedResidual α l0 l1 l2 c β) B A :=
        (tailIntegral_eq_intervalIntegral
          (weightedResidual_continuous α l0 l1 l2 c β) B A).symm
      _ = 0 := htailA
  exact compact_onePiece_residual_impossible α γ l0 l1 l2 c β A B
    hα hγ0 hγ1 hAB hl2 hrA hrB hrA' hrB' hzero

end CompactOnePiece

/-! ## Flattened source: `lean_ii/GammaBounds.lean` -/


open Set

namespace CompactOnePiece

private lemma exists_nonzero_mem_Icc {A B : ℝ} (hAB : A < B) :
    ∃ x ∈ Icc A B, x ≠ 0 := by
  by_cases hA : A = 0
  · exact ⟨B, right_mem_Icc.mpr hAB.le, by linarith⟩
  · exact ⟨A, left_mem_Icc.mpr hAB.le, hA⟩

/-- The number `γ = E[X² exp(-α|X|)]` lies strictly between zero and one for
a nondegenerate compact isotropic log-affine law. -/
theorem gamma_mem_Ioo
    (α c β A B γ : ℝ) (hα : 0 < α) (hAB : A < B)
    (hvariance :
      (∫ x in A..B, x ^ 2 * exponentialWeight c β x) = 1)
    (hgamma :
      (∫ x in A..B,
        x ^ 2 * Real.exp (-α * |x|) * exponentialWeight c β x) = γ) :
    γ ∈ Ioo (0 : ℝ) 1 := by
  let D : ℝ → ℝ := fun x ↦
    x ^ 2 * Real.exp (-α * |x|) * exponentialWeight c β x
  let V : ℝ → ℝ := fun x ↦ x ^ 2 * exponentialWeight c β x
  have hD : Continuous D := by
    dsimp [D]
    have he : Continuous (fun y : ℝ ↦ Real.exp (-α * |y|)) := by fun_prop
    exact ((continuous_id.pow 2).mul he).mul (exponentialWeight_continuous c β)
  have hV : Continuous V := by
    dsimp [V]
    exact (continuous_id.pow 2).mul (exponentialWeight_continuous c β)
  obtain ⟨x, hx, hx0⟩ := exists_nonzero_mem_Icc hAB
  have hxabs : 0 < |x| := abs_pos.mpr hx0
  have hexp0 : 0 < Real.exp (-α * |x|) := Real.exp_pos _
  have hDx : 0 < D x := by
    dsimp [D]
    exact mul_pos (mul_pos (sq_pos_of_ne_zero hx0) hexp0)
      (exponentialWeight_pos c β x)
  have hDpos : 0 < ∫ y in A..B, D y := by
    apply intervalIntegral.integral_pos hAB hD.continuousOn
    · intro y _
      dsimp [D]
      exact mul_nonneg (mul_nonneg (sq_nonneg y) (Real.exp_pos _).le)
        (exponentialWeight_pos c β y).le
    · exact ⟨x, hx, hDx⟩
  have hDV : ∀ y ∈ Ioc A B, D y ≤ V y := by
    intro y _
    dsimp [D, V]
    have he : Real.exp (-α * |y|) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα.le) (abs_nonneg y))
    have hbase : 0 ≤ y ^ 2 * exponentialWeight c β y :=
      mul_nonneg (sq_nonneg y) (exponentialWeight_pos c β y).le
    calc
      y ^ 2 * Real.exp (-α * |y|) * exponentialWeight c β y =
          (y ^ 2 * exponentialWeight c β y) * Real.exp (-α * |y|) := by ring
      _ ≤ (y ^ 2 * exponentialWeight c β y) * 1 :=
        mul_le_mul_of_nonneg_left he hbase
      _ = y ^ 2 * exponentialWeight c β y := by ring
  have hexplt : Real.exp (-α * |x|) < 1 := by
    rw [← Real.exp_zero]
    have hnegα : -α < 0 := by linarith
    exact Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos hnegα hxabs)
  have hDxVx : D x < V x := by
    dsimp [D, V]
    have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
    have hw := exponentialWeight_pos c β x
    have hbase : 0 < x ^ 2 * exponentialWeight c β x := mul_pos hx2 hw
    calc
      x ^ 2 * Real.exp (-α * |x|) * exponentialWeight c β x =
          (x ^ 2 * exponentialWeight c β x) * Real.exp (-α * |x|) := by ring
      _ < (x ^ 2 * exponentialWeight c β x) * 1 :=
        mul_lt_mul_of_pos_left hexplt hbase
      _ = x ^ 2 * exponentialWeight c β x := by ring
  have hlt : (∫ y in A..B, D y) < ∫ y in A..B, V y :=
    intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hAB hD.continuousOn hV.continuousOn hDV ⟨x, hx, hDxVx⟩
  change (∫ y in A..B, D y) = γ at hgamma
  change (∫ y in A..B, V y) = 1 at hvariance
  constructor <;> linarith

end CompactOnePiece

/-! ## Flattened source: `lean_ii/MultiplierIdentity.lean` -/


namespace CompactOnePiece

noncomputable def rawResidualSlope (α l1 l2 x : ℝ) : ℝ :=
  -α ^ 2 * x * Real.exp (-α * |x|) - l1 - 2 * l2 * x

noncomputable def rawWeightedResidualDerivative
    (α l0 l1 l2 c β x : ℝ) : ℝ :=
  (rawResidualSlope α l1 l2 x + β * residual α l0 l1 l2 x) *
    exponentialWeight c β x

lemma rawWeightedResidualDerivative_continuous (α l0 l1 l2 c β : ℝ) :
    Continuous (rawWeightedResidualDerivative α l0 l1 l2 c β) := by
  unfold rawWeightedResidualDerivative rawResidualSlope
  have hs : Continuous (fun x : ℝ ↦
      -α ^ 2 * x * Real.exp (-α * |x|) - l1 - 2 * l2 * x) := by fun_prop
  exact (hs.add ((residual_continuous α l0 l1 l2).const_mul β)).mul
    (exponentialWeight_continuous c β)

lemma hasDerivAt_weightedResidual_raw
    (α l0 l1 l2 c β x : ℝ) :
    HasDerivAt (weightedResidual α l0 l1 l2 c β)
      (rawWeightedResidualDerivative α l0 l1 l2 c β x) x := by
  have h := (hasDerivAt_residual α l0 l1 l2 x).mul
    (hasDerivAt_exponentialWeight c β x)
  have h' := h.congr_deriv (show
      (-α ^ 2 * x * Real.exp (-α * |x|) - l1 - 2 * l2 * x) *
          exponentialWeight c β x +
          residual α l0 l1 l2 x * (β * exponentialWeight c β x) =
        rawWeightedResidualDerivative α l0 l1 l2 c β x by
    unfold rawWeightedResidualDerivative rawResidualSlope
    ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [weightedResidual]

/-- Integration by parts converts the two residual moment equations and the
two endpoint equations into `∫ x r'(x)f(x)=0`. -/
theorem raw_residual_integration_by_parts
    (α l0 l1 l2 c β A B : ℝ)
    (hrA : residual α l0 l1 l2 A = 0)
    (hrB : residual α l0 l1 l2 B = 0)
    (hres0 :
      (∫ x in A..B,
        residual α l0 l1 l2 x * exponentialWeight c β x) = 0)
    (hres1 :
      (∫ x in A..B,
        x * residual α l0 l1 l2 x * exponentialWeight c β x) = 0) :
    (∫ x in A..B,
      x * rawResidualSlope α l1 l2 x * exponentialWeight c β x) = 0 := by
  let R := weightedResidual α l0 l1 l2 c β
  let R' := rawWeightedResidualDerivative α l0 l1 l2 c β
  have hRcont : Continuous R := weightedResidual_continuous α l0 l1 l2 c β
  have hR'cont : Continuous R' :=
    rawWeightedResidualDerivative_continuous α l0 l1 l2 c β
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := A) (b := B) (u := fun x : ℝ ↦ x) (u' := fun _ : ℝ ↦ 1)
    (v := R) (v' := R')
    (fun x _ ↦ hasDerivAt_id x)
    (fun x _ ↦ hasDerivAt_weightedResidual_raw α l0 l1 l2 c β x)
    (continuous_const.intervalIntegrable A B)
    (hR'cont.intervalIntegrable A B)
  have hRint : (∫ x in A..B, R x) = 0 := by
    calc
      (∫ x in A..B, R x) =
          ∫ x in A..B, residual α l0 l1 l2 x * exponentialWeight c β x := by
        apply intervalIntegral.integral_congr
        intro x _
        rfl
      _ = 0 := hres0
  have hip0 : (∫ x in A..B, x * R' x) = 0 := by
    rw [hip]
    have hRA : R A = 0 := by simp [R, weightedResidual, hrA]
    have hRB : R B = 0 := by simp [R, weightedResidual, hrB]
    have hOne : (∫ x in A..B, 1 * R x) = ∫ x in A..B, R x := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    rw [hRA, hRB, hOne, hRint]
    ring
  have hmain : Continuous (fun x : ℝ ↦
      x * rawResidualSlope α l1 l2 x * exponentialWeight c β x) := by
    unfold rawResidualSlope exponentialWeight
    fun_prop
  have hcorr : Continuous (fun x : ℝ ↦
      x * residual α l0 l1 l2 x * exponentialWeight c β x) := by
    exact (continuous_id.mul (residual_continuous α l0 l1 l2)).mul
      (exponentialWeight_continuous c β)
  have hdecomp : (fun x : ℝ ↦ x * R' x) = fun x ↦
      x * rawResidualSlope α l1 l2 x * exponentialWeight c β x +
        β * (x * residual α l0 l1 l2 x * exponentialWeight c β x) := by
    funext x
    simp only [R', rawWeightedResidualDerivative]
    ring
  rw [hdecomp,
    intervalIntegral.integral_add (hmain.intervalIntegrable A B)
      ((hcorr.const_mul β).intervalIntegrable A B),
    intervalIntegral.integral_const_mul, hres1, mul_zero, add_zero] at hip0
  exact hip0

/-- The short algebraic part of the integration-by-parts calculation.  The
identity `hibp` is `∫ x r'(x)f(x)=0`; the other three hypotheses are the mean,
variance, and definition of `γ`. -/
theorem multiplier_identity_of_moments
    (α γ l1 l2 A B : ℝ) (w : ℝ → ℝ) (hw : Continuous w)
    (hmean : (∫ x in A..B, x * w x) = 0)
    (hvariance : (∫ x in A..B, x ^ 2 * w x) = 1)
    (hgamma : (∫ x in A..B, x ^ 2 * Real.exp (-α * |x|) * w x) = γ)
    (hibp : (∫ x in A..B, x * rawResidualSlope α l1 l2 x * w x) = 0) :
    2 * l2 = -α ^ 2 * γ := by
  let G : ℝ → ℝ := fun x ↦ x ^ 2 * Real.exp (-α * |x|) * w x
  let M : ℝ → ℝ := fun x ↦ x * w x
  let V : ℝ → ℝ := fun x ↦ x ^ 2 * w x
  have hG : Continuous G := by
    dsimp [G]
    have he : Continuous (fun x : ℝ ↦ Real.exp (-α * |x|)) := by fun_prop
    exact (((continuous_id.pow 2).mul he).mul hw)
  have hM : Continuous M := by
    dsimp [M]
    exact continuous_id.mul hw
  have hV : Continuous V := by
    dsimp [V]
    exact (continuous_id.pow 2).mul hw
  have hdecomp :
      (fun x ↦ x * rawResidualSlope α l1 l2 x * w x) =
        (fun x ↦ (-α ^ 2) * G x - l1 * M x - (2 * l2) * V x) := by
    funext x
    dsimp [G, M, V, rawResidualSlope]
    ring
  rw [hdecomp] at hibp
  have hGI : IntervalIntegrable G MeasureTheory.volume A B :=
    hG.intervalIntegrable (μ := MeasureTheory.volume) A B
  have hMI : IntervalIntegrable M MeasureTheory.volume A B :=
    hM.intervalIntegrable (μ := MeasureTheory.volume) A B
  have hVI : IntervalIntegrable V MeasureTheory.volume A B :=
    hV.intervalIntegrable (μ := MeasureTheory.volume) A B
  rw [intervalIntegral.integral_sub
        ((hGI.const_mul (-α ^ 2)).sub (hMI.const_mul l1)) (hVI.const_mul (2 * l2)),
      intervalIntegral.integral_sub
        (hGI.const_mul (-α ^ 2)) (hMI.const_mul l1),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hibp
  change (∫ x in A..B, G x) = γ at hgamma
  change (∫ x in A..B, M x) = 0 at hmean
  change (∫ x in A..B, V x) = 1 at hvariance
  rw [hgamma, hmean, hvariance] at hibp
  nlinarith

end CompactOnePiece

/-! ## Flattened source: `lean_ii/ClaimIIComplete.lean` -/


open Set

namespace CompactOnePiece

/-- Fully assembled deterministic contradiction for the compact one-piece
case.  These hypotheses are exactly the moment, endpoint, and hinge identities
delivered by the finite-dimensional variational argument. -/
theorem no_compact_onePiece_stationary_point
    (α γ l0 l1 l2 c β A B : ℝ)
    (hα : 0 < α) (hAB : A < B)
    (hmean :
      (∫ x in A..B, x * exponentialWeight c β x) = 0)
    (hvariance :
      (∫ x in A..B, x ^ 2 * exponentialWeight c β x) = 1)
    (hgamma :
      (∫ x in A..B,
        x ^ 2 * Real.exp (-α * |x|) * exponentialWeight c β x) = γ)
    (hrA : residual α l0 l1 l2 A = 0)
    (hrB : residual α l0 l1 l2 B = 0)
    (htailA : tailIntegral (weightedResidual α l0 l1 l2 c β) B A = 0)
    (hmomentA : tailMoment (weightedResidual α l0 l1 l2 c β) B A = 0)
    (hQ : ∀ s ∈ Icc A B,
      0 ≤ hingeQ (weightedResidual α l0 l1 l2 c β) B s) : False := by
  have hγ := gamma_mem_Ioo α c β A B γ hα hAB hvariance hgamma
  have hres0 :
      (∫ x in A..B,
        residual α l0 l1 l2 x * exponentialWeight c β x) = 0 := by
    calc
      (∫ x in A..B, residual α l0 l1 l2 x * exponentialWeight c β x) =
          ∫ x in A..B, weightedResidual α l0 l1 l2 c β x := by
        apply intervalIntegral.integral_congr
        intro x _
        unfold weightedResidual
        ring
      _ = tailIntegral (weightedResidual α l0 l1 l2 c β) B A :=
        (tailIntegral_eq_intervalIntegral
          (weightedResidual_continuous α l0 l1 l2 c β) B A).symm
      _ = 0 := htailA
  have hres1 :
      (∫ x in A..B,
        x * residual α l0 l1 l2 x * exponentialWeight c β x) = 0 := by
    calc
      (∫ x in A..B, x * residual α l0 l1 l2 x * exponentialWeight c β x) =
          ∫ x in A..B, x * weightedResidual α l0 l1 l2 c β x := by
        apply intervalIntegral.integral_congr
        intro x _
        unfold weightedResidual
        ring
      _ = tailMoment (weightedResidual α l0 l1 l2 c β) B A :=
        (tailMoment_eq_intervalIntegral
          (weightedResidual_continuous α l0 l1 l2 c β) B A).symm
      _ = 0 := hmomentA
  have hibp := raw_residual_integration_by_parts α l0 l1 l2 c β A B
    hrA hrB hres0 hres1
  have hl2 := multiplier_identity_of_moments α γ l1 l2 A B
    (exponentialWeight c β) (exponentialWeight_continuous c β)
    hmean hvariance hgamma hibp
  exact compact_onePiece_residual_impossible_of_hinge
    α γ l0 l1 l2 c β A B hα hγ.1 hγ.2 hAB hl2
    hrA hrB htailA hmomentA hQ

/-- Equivalent interface matching the output of the parameter-space
variational calculation: two residual moments and the full-support hinge
inequality. -/
theorem no_compact_onePiece_stationary_point_of_integrals
    (α γ l0 l1 l2 c β A B : ℝ)
    (hα : 0 < α) (hAB : A < B)
    (hmean :
      (∫ x in A..B, x * exponentialWeight c β x) = 0)
    (hvariance :
      (∫ x in A..B, x ^ 2 * exponentialWeight c β x) = 1)
    (hgamma :
      (∫ x in A..B,
        x ^ 2 * Real.exp (-α * |x|) * exponentialWeight c β x) = γ)
    (hrA : residual α l0 l1 l2 A = 0)
    (hrB : residual α l0 l1 l2 B = 0)
    (hres0 :
      (∫ x in A..B,
        residual α l0 l1 l2 x * exponentialWeight c β x) = 0)
    (hres1 :
      (∫ x in A..B,
        x * residual α l0 l1 l2 x * exponentialWeight c β x) = 0)
    (hhinge : ∀ s ∈ Ioo A B,
      0 ≤ ∫ x in A..B,
        max (x - s) 0 *
          (residual α l0 l1 l2 x * exponentialWeight c β x)) : False := by
  let R := weightedResidual α l0 l1 l2 c β
  have hR : Continuous R := weightedResidual_continuous α l0 l1 l2 c β
  have htailA : tailIntegral R B A = 0 := by
    rw [tailIntegral_eq_intervalIntegral hR]
    simpa [R, weightedResidual] using hres0
  have hmomentA : tailMoment R B A = 0 := by
    rw [tailMoment_eq_intervalIntegral hR]
    simpa [R, weightedResidual, mul_assoc] using hres1
  have hQ : ∀ s ∈ Icc A B, 0 ≤ hingeQ R B s := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with rfl | hAs
    · simp [hingeQ, htailA, hmomentA]
    rcases eq_or_lt_of_le hs.2 with rfl | hsB
    · simp [hingeQ]
    rw [← integral_max_sub_eq_hingeQ hR hs]
    simpa [R, weightedResidual, mul_assoc] using hhinge s ⟨hAs, hsB⟩
  exact no_compact_onePiece_stationary_point
    α γ l0 l1 l2 c β A B hα hAB hmean hvariance hgamma
    hrA hrB htailA hmomentA hQ

end CompactOnePiece

/-! ## Flattened source: `lean_ii/StationarityBridge.lean` -/


open Set

namespace CompactOnePiece

private lemma intervalIntegral_sub_explicit
    {f g : ℝ → ℝ} {A B : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume A B)
    (hg : IntervalIntegrable g MeasureTheory.volume A B) :
    (∫ x in A..B, f x - g x) =
      (∫ x in A..B, f x) - ∫ x in A..B, g x := by
  calc
    (∫ x in A..B, f x - g x) = ∫ x in A..B, (f - g) x := by
      apply intervalIntegral.integral_congr
      intro x _
      rfl
    _ = (∫ x in A..B, f x) - ∫ x in A..B, g x :=
      intervalIntegral.integral_sub hf hg

private lemma intervalIntegral_const_mul_explicit
    (a : ℝ) (f : ℝ → ℝ) (A B : ℝ) :
    (∫ x in A..B, a * f x) = a * ∫ x in A..B, f x := by
  exact intervalIntegral.integral_const_mul a f

/-- Linearity of integration, packaged in the form used to convert the
finite-dimensional stationarity equations into residual moment equations. -/
lemma integral_mul_residual_eq
    (q : ℝ → ℝ) (hq : Continuous q)
    (α l0 l1 l2 c β A B : ℝ) :
    (∫ x in A..B,
      q x * residual α l0 l1 l2 x * exponentialWeight c β x) =
      (∫ x in A..B, q x * smoothG α x * exponentialWeight c β x) -
      l0 * (∫ x in A..B, q x * exponentialWeight c β x) -
      l1 * (∫ x in A..B, q x * x * exponentialWeight c β x) -
      l2 * (∫ x in A..B, q x * x ^ 2 * exponentialWeight c β x) := by
  let G : ℝ → ℝ := fun x ↦ q x * smoothG α x * exponentialWeight c β x
  let M₀ : ℝ → ℝ := fun x ↦ q x * exponentialWeight c β x
  let M₁ : ℝ → ℝ := fun x ↦ q x * x * exponentialWeight c β x
  let M₂ : ℝ → ℝ := fun x ↦ q x * x ^ 2 * exponentialWeight c β x
  have hG : Continuous G := by
    dsimp [G]
    exact (hq.mul (smoothG_continuous α)).mul (exponentialWeight_continuous c β)
  have hM₀ : Continuous M₀ := by
    dsimp [M₀]
    exact hq.mul (exponentialWeight_continuous c β)
  have hM₁ : Continuous M₁ := by
    dsimp [M₁]
    exact (hq.mul continuous_id).mul (exponentialWeight_continuous c β)
  have hM₂ : Continuous M₂ := by
    dsimp [M₂]
    exact (hq.mul (continuous_id.pow 2)).mul (exponentialWeight_continuous c β)
  have hpoint : (fun x ↦
      q x * residual α l0 l1 l2 x * exponentialWeight c β x) =
      fun x ↦ G x - l0 * M₀ x - l1 * M₁ x - l2 * M₂ x := by
    funext x
    dsimp [G, M₀, M₁, M₂, residual]
    ring
  rw [hpoint]
  have hC0 : Continuous (fun x : ℝ ↦ G x - l0 * M₀ x) := by
    exact (hG.sub (hM₀.const_mul l0)).congr (fun x ↦ rfl)
  have hC1 : Continuous (fun x : ℝ ↦ G x - l0 * M₀ x - l1 * M₁ x) := by
    exact (hC0.sub (hM₁.const_mul l1)).congr (fun x ↦ rfl)
  calc
    (∫ x in A..B, G x - l0 * M₀ x - l1 * M₁ x - l2 * M₂ x) =
        (∫ x in A..B, G x - l0 * M₀ x - l1 * M₁ x) -
          ∫ x in A..B, l2 * M₂ x :=
      intervalIntegral_sub_explicit
        (hC1.intervalIntegrable (μ := MeasureTheory.volume) A B)
        ((hM₂.const_mul l2).intervalIntegrable (μ := MeasureTheory.volume) A B)
    _ = ((∫ x in A..B, G x - l0 * M₀ x) -
          ∫ x in A..B, l1 * M₁ x) - ∫ x in A..B, l2 * M₂ x := by
      rw [intervalIntegral_sub_explicit
        (hC0.intervalIntegrable (μ := MeasureTheory.volume) A B)
        ((hM₁.const_mul l1).intervalIntegrable (μ := MeasureTheory.volume) A B)]
    _ = (((∫ x in A..B, G x) - ∫ x in A..B, l0 * M₀ x) -
          ∫ x in A..B, l1 * M₁ x) - ∫ x in A..B, l2 * M₂ x := by
      rw [intervalIntegral_sub_explicit
        (hG.intervalIntegrable (μ := MeasureTheory.volume) A B)
        ((hM₀.const_mul l0).intervalIntegrable (μ := MeasureTheory.volume) A B)]
    _ = (∫ x in A..B, q x * smoothG α x * exponentialWeight c β x) -
          l0 * (∫ x in A..B, q x * exponentialWeight c β x) -
          l1 * (∫ x in A..B, q x * x * exponentialWeight c β x) -
          l2 * (∫ x in A..B, q x * x ^ 2 * exponentialWeight c β x) := by
      rw [intervalIntegral_const_mul_explicit,
        intervalIntegral_const_mul_explicit,
        intervalIntegral_const_mul_explicit]

/-- Algebraic bridge from the stationarity equations in the `c`, `β`,
endpoint, and hinge directions to the deterministic contradiction. -/
theorem no_compact_onePiece_of_stationarity_equations
    (α γ l0 l1 l2 c β A B : ℝ)
    (hα : 0 < α) (hAB : A < B)
    (hmean :
      (∫ x in A..B, x * exponentialWeight c β x) = 0)
    (hvariance :
      (∫ x in A..B, x ^ 2 * exponentialWeight c β x) = 1)
    (hgamma :
      (∫ x in A..B,
        x ^ 2 * Real.exp (-α * |x|) * exponentialWeight c β x) = γ)
    (hc :
      (∫ x in A..B, smoothG α x * exponentialWeight c β x) =
        l0 * (∫ x in A..B, exponentialWeight c β x) +
        l1 * (∫ x in A..B, x * exponentialWeight c β x) +
        l2 * (∫ x in A..B, x ^ 2 * exponentialWeight c β x))
    (hβ :
      (∫ x in A..B, x * smoothG α x * exponentialWeight c β x) =
        l0 * (∫ x in A..B, x * exponentialWeight c β x) +
        l1 * (∫ x in A..B, x ^ 2 * exponentialWeight c β x) +
        l2 * (∫ x in A..B, x ^ 3 * exponentialWeight c β x))
    (hA : smoothG α A = l0 + l1 * A + l2 * A ^ 2)
    (hB : smoothG α B = l0 + l1 * B + l2 * B ^ 2)
    (hhinge : ∀ s ∈ Ioo A B,
      l0 * (∫ x in A..B, max (x - s) 0 * exponentialWeight c β x) +
        l1 * (∫ x in A..B,
          max (x - s) 0 * x * exponentialWeight c β x) +
        l2 * (∫ x in A..B,
          max (x - s) 0 * x ^ 2 * exponentialWeight c β x) ≤
        ∫ x in A..B,
          max (x - s) 0 * smoothG α x * exponentialWeight c β x) : False := by
  have hres0 :
      (∫ x in A..B,
        residual α l0 l1 l2 x * exponentialWeight c β x) = 0 := by
    have h := integral_mul_residual_eq (fun _ : ℝ ↦ 1) continuous_const
      α l0 l1 l2 c β A B
    simp only [one_mul] at h
    rw [h, hc]
    ring
  have hres1 :
      (∫ x in A..B,
        x * residual α l0 l1 l2 x * exponentialWeight c β x) = 0 := by
    have h := integral_mul_residual_eq (fun x : ℝ ↦ x) continuous_id
      α l0 l1 l2 c β A B
    have hm1 :
        (∫ x in A..B, x * x * exponentialWeight c β x) =
          ∫ x in A..B, x ^ 2 * exponentialWeight c β x := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    have hm2 :
        (∫ x in A..B, x * x ^ 2 * exponentialWeight c β x) =
          ∫ x in A..B, x ^ 3 * exponentialWeight c β x := by
      apply intervalIntegral.integral_congr
      intro x _
      ring
    rw [h, hm1, hm2, hβ]
    ring
  have hrA : residual α l0 l1 l2 A = 0 := by
    unfold residual
    rw [hA]
    ring
  have hrB : residual α l0 l1 l2 B = 0 := by
    unfold residual
    rw [hB]
    ring
  have hresHinge : ∀ s ∈ Ioo A B,
      0 ≤ ∫ x in A..B,
        max (x - s) 0 *
          (residual α l0 l1 l2 x * exponentialWeight c β x) := by
    intro s hs
    have hq : Continuous (fun x : ℝ ↦ max (x - s) 0) := by fun_prop
    have h := integral_mul_residual_eq (fun x : ℝ ↦ max (x - s) 0) hq
      α l0 l1 l2 c β A B
    have h' :
        (∫ x in A..B,
          max (x - s) 0 *
            (residual α l0 l1 l2 x * exponentialWeight c β x)) =
          (∫ x in A..B,
            max (x - s) 0 * smoothG α x * exponentialWeight c β x) -
          l0 * (∫ x in A..B,
            max (x - s) 0 * exponentialWeight c β x) -
          l1 * (∫ x in A..B,
            max (x - s) 0 * x * exponentialWeight c β x) -
          l2 * (∫ x in A..B,
            max (x - s) 0 * x ^ 2 * exponentialWeight c β x) := by
      simpa only [mul_assoc] using h
    rw [h']
    have hv := hhinge s hs
    nlinarith
  exact no_compact_onePiece_stationary_point_of_integrals
    α γ l0 l1 l2 c β A B hα hAB hmean hvariance hgamma
    hrA hrB hres0 hres1 hresHinge

end CompactOnePiece

/-! ## Flattened source: `lean_ii/SmoothGEquality.lean` -/


open Set

namespace CompactOnePiece

/-- The function appearing in the extremal problem. -/
noncomputable def explicitG (α x : ℝ) : ℝ :=
  (1 + α * |x|) * Real.exp (-α * |x|)

private noncomputable def positiveBranch (α x : ℝ) : ℝ :=
  (1 + α * x) * Real.exp (-α * x)

private noncomputable def negativeBranch (α x : ℝ) : ℝ :=
  (1 - α * x) * Real.exp (α * x)

private lemma explicitG_eq_positiveBranch (α : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    explicitG α x = positiveBranch α x := by
  simp [explicitG, positiveBranch, abs_of_nonneg hx]

private lemma explicitG_eq_negativeBranch (α : ℝ) {x : ℝ} (hx : x ≤ 0) :
    explicitG α x = negativeBranch α x := by
  unfold explicitG negativeBranch
  rw [abs_of_nonpos hx]
  have he : -α * -x = α * x := by ring
  rw [he]
  ring

private lemma hasDerivAt_positiveBranch (α x : ℝ) :
    HasDerivAt (positiveBranch α)
      (-α ^ 2 * x * Real.exp (-α * x)) x := by
  have hlin0 := (hasDerivAt_const x 1).add
    ((hasDerivAt_const x α).mul (hasDerivAt_id x))
  have hlin1 := hlin0.congr_deriv (show 0 + (0 * x + α * 1) = α by ring)
  have hlin : HasDerivAt (fun y : ℝ ↦ 1 + α * y) α x := by
    apply hlin1.congr_of_eventuallyEq
    filter_upwards [] with y
    simp
  have harg := (hasDerivAt_id x).const_mul (-α)
  have hexp0 := (Real.hasDerivAt_exp (-α * x)).comp x harg
  have hexp1 := hexp0.congr_deriv (show
      Real.exp (-α * x) * (-α * 1) = -α * Real.exp (-α * x) by ring)
  have hexp : HasDerivAt (fun y : ℝ ↦ Real.exp (-α * y))
      (-α * Real.exp (-α * x)) x := by
    apply hexp1.congr_of_eventuallyEq
    filter_upwards [] with y
    simp [Function.comp_apply]
  have h := hlin.mul hexp
  have h' := h.congr_deriv (show
      α * Real.exp (-α * x) + (1 + α * x) * (-α * Real.exp (-α * x)) =
        -α ^ 2 * x * Real.exp (-α * x) by ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [positiveBranch]

private lemma hasDerivAt_negativeBranch (α x : ℝ) :
    HasDerivAt (negativeBranch α)
      (-α ^ 2 * x * Real.exp (α * x)) x := by
  have hlin0 := (hasDerivAt_const x 1).sub
    ((hasDerivAt_const x α).mul (hasDerivAt_id x))
  have hlin1 := hlin0.congr_deriv (show 0 - (0 * x + α * 1) = -α by ring)
  have hlin : HasDerivAt (fun y : ℝ ↦ 1 - α * y) (-α) x := by
    apply hlin1.congr_of_eventuallyEq
    filter_upwards [] with y
    simp
  have harg := (hasDerivAt_id x).const_mul α
  have hexp0 := (Real.hasDerivAt_exp (α * x)).comp x harg
  have hexp1 := hexp0.congr_deriv (show
      Real.exp (α * x) * (α * 1) = α * Real.exp (α * x) by ring)
  have hexp : HasDerivAt (fun y : ℝ ↦ Real.exp (α * y))
      (α * Real.exp (α * x)) x := by
    apply hexp1.congr_of_eventuallyEq
    filter_upwards [] with y
    simp [Function.comp_apply]
  have h := hlin.mul hexp
  have h' := h.congr_deriv (show
      -α * Real.exp (α * x) + (1 - α * x) * (α * Real.exp (α * x)) =
        -α ^ 2 * x * Real.exp (α * x) by ring)
  apply h'.congr_of_eventuallyEq
  filter_upwards [] with y
  simp [negativeBranch]

/-- The absolute-value formula is differentiable even at the origin. -/
lemma hasDerivAt_explicitG (α x : ℝ) :
    HasDerivAt (explicitG α)
      (-α ^ 2 * x * Real.exp (-α * |x|)) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have h := (hasDerivAt_negativeBranch α x).hasDerivWithinAt.congr
      (fun y hy ↦ explicitG_eq_negativeBranch α hy)
      (explicitG_eq_negativeBranch α hx.le)
    have h' := h.hasDerivAt (Iic_mem_nhds hx)
    apply h'.congr_deriv
    rw [abs_of_neg hx]
    have he : -α * -x = α * x := by ring
    rw [he]
  · have hn0 : HasDerivAt (negativeBranch α) 0 0 :=
      (hasDerivAt_negativeBranch α 0).congr_deriv (by ring)
    have hp0 : HasDerivAt (positiveBranch α) 0 0 :=
      (hasDerivAt_positiveBranch α 0).congr_deriv (by ring)
    have hneg := hn0.hasDerivWithinAt.congr
      (fun y hy ↦ explicitG_eq_negativeBranch α hy)
      (explicitG_eq_negativeBranch α le_rfl)
    have hpos := hp0.hasDerivWithinAt.congr
      (fun y hy ↦ explicitG_eq_positiveBranch α hy)
      (explicitG_eq_positiveBranch α le_rfl)
    change HasDerivWithinAt (explicitG α) 0 (Iic 0) 0 at hneg
    change HasDerivWithinAt (explicitG α) 0 (Ici 0) 0 at hpos
    have hu : HasDerivWithinAt (explicitG α) 0 (Set.univ : Set ℝ) 0 := by
      simpa only [Iic_union_Ici] using hneg.union hpos
    have hu' : HasDerivAt (explicitG α) 0 0 := by
      simpa only [hasDerivWithinAt_univ] using hu
    exact hu'.congr_deriv (by ring)
  · have h := (hasDerivAt_positiveBranch α x).hasDerivWithinAt.congr
      (fun y hy ↦ explicitG_eq_positiveBranch α hy)
      (explicitG_eq_positiveBranch α hx.le)
    have h' := h.hasDerivAt (Ici_mem_nhds hx)
    apply h'.congr_deriv
    rw [abs_of_pos hx]

/-- The integral presentation used to avoid differentiating `|x|` is exactly
the elementary function in the statement of the theorem. -/
theorem smoothG_eq_explicitG (α x : ℝ) : smoothG α x = explicitG α x := by
  let d : ℝ → ℝ := fun y ↦ smoothG α y - explicitG α y
  have hd : Differentiable ℝ d := fun y ↦
    ((hasDerivAt_smoothG α y).sub (hasDerivAt_explicitG α y)).differentiableAt
  have hd0 : ∀ y, deriv d y = 0 := by
    intro y
    exact (((hasDerivAt_smoothG α y).sub
      (hasDerivAt_explicitG α y)).deriv.trans (by ring))
  have hconst := is_const_of_deriv_eq_zero hd hd0 x 0
  change smoothG α x - explicitG α x = smoothG α 0 - explicitG α 0 at hconst
  have hbase : smoothG α 0 - explicitG α 0 = 0 := by
    simp [smoothG, explicitG]
  rw [hbase] at hconst
  exact sub_eq_zero.mp hconst

end CompactOnePiece

/-! ## Flattened source: `lean_ii/ClaimIILocalMax.lean` -/


open Filter Set MeasureTheory
open scoped Topology Interval

namespace CompactOnePiece

open LogConcaveExtremum
open LogConcaveExtremum.CompactSplitIntegral
open LogConcaveExtremum.CompactMomentMap
open LogConcaveExtremum.Variational


/-- The endpoints must continue to straddle the fixed hinge point. -/
def splitDomain (s : ℝ) : Set Param :=
  {p | corrCLM 1 p < s ∧ s < corrCLM 2 p}

lemma splitDomain_mem_nhds_base
    (c A B s : ℝ) (hs : s ∈ Ioo A B) :
    splitDomain s ∈ 𝓝 (baseParam c A B) := by
  have hopen : IsOpen (splitDomain s) := by
    exact (isOpen_lt (corrCLM 1).continuous continuous_const).inter
      (isOpen_lt continuous_const (corrCLM 2).continuous)
  apply hopen.mem_nhds
  simpa [splitDomain] using hs

/-- Coordinate expansion of a continuous linear functional on `Fin 3 → ℝ`. -/
lemma dual_corr_apply (L : StrongDual ℝ Corr) (v : Corr) :
    L v = L (corrTriple 1 0 0) * v 0 +
      L (corrTriple 0 1 0) * v 1 +
      L (corrTriple 0 0 1) * v 2 := by
  have hv : v = v 0 • corrTriple 1 0 0 +
      v 1 • corrTriple 0 1 0 + v 2 • corrTriple 0 0 1 := by
    funext i
    fin_cases i <;> simp [corrTriple]
  calc
    L v = L (v 0 • corrTriple 1 0 0 +
        v 1 • corrTriple 0 1 0 + v 2 • corrTriple 0 0 1) := congrArg L hv
    _ = L (corrTriple 1 0 0) * v 0 +
        L (corrTriple 0 1 0) * v 1 +
        L (corrTriple 0 0 1) * v 2 := by
      rw [map_add, map_add, map_smul, map_smul, map_smul]
      ring

lemma integral_max_sub_exp_eq_tail
    (q : ℝ → ℝ) (hq : Continuous q) (c beta : ℝ)
    {A B s : ℝ} (hs : s ∈ Icc A B) :
    (∫ x in A..B, max (x - s) 0 * q x * Real.exp (c + beta * x)) =
      ∫ x in s..B, (x - s) * q x * Real.exp (c + beta * x) := by
  let R : ℝ → ℝ := fun x ↦ q x * Real.exp (c + beta * x)
  have hR : Continuous R := by
    dsimp [R]
    fun_prop
  calc
    (∫ x in A..B, max (x - s) 0 * q x * Real.exp (c + beta * x)) =
        ∫ x in A..B, max (x - s) 0 * R x := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp [R]
      ring
    _ = hingeQ R B s := integral_max_sub_eq_hingeQ hR hs
    _ = ∫ x in s..B, (x - s) * R x := hingeQ_eq_intervalIntegral hR B s
    _ = ∫ x in s..B, (x - s) * q x * Real.exp (c + beta * x) := by
      apply intervalIntegral.integral_congr
      intro x _
      dsimp [R]
      ring

lemma splitIntegral_explicitG_eq_smoothG (α beta s : ℝ) :
    splitIntegral (explicitG α) beta s = splitIntegral (smoothG α) beta s := by
  funext p
  unfold splitIntegral
  congr 1
  · apply intervalIntegral.integral_congr
    intro x _
    unfold leftIntegrand
    rw [smoothG_eq_explicitG]
  · apply intervalIntegral.integral_congr
    intro x _
    unfold rightIntegrand
    rw [smoothG_eq_explicitG]

/-- A compact, one-piece log-affine isotropic density cannot be a local
maximizer against all one-sided hinge perturbations. -/
theorem no_compact_onePiece_localMax
    (α c beta A B : ℝ) (hα : 0 < α) (hAB : A < B)
    (hmass : (∫ x in A..B, Real.exp (c + beta * x)) = 1)
    (hmean : (∫ x in A..B, x * Real.exp (c + beta * x)) = 0)
    (hsecond : (∫ x in A..B, x ^ 2 * Real.exp (c + beta * x)) = 1)
    (hmax : ∀ s ∈ Ioo A B,
      IsLocalMaxOn (splitIntegral (smoothG α) beta s)
        (splitDomain s ∩
          ({p | momentMap beta s p = momentMap beta s (baseParam c A B)} ∩
            {p | 0 ≤ p.1.2}))
        (baseParam c A B)) : False := by
  let s0 := (A + B) / 2
  have hs0 : s0 ∈ Ioo A B := by
    dsimp [s0]
    constructor <;> linarith
  let objD (s : ℝ) := splitIntegralFDeriv (smoothG α) c beta A B s
  let momD (s : ℝ) := momentFDeriv c beta A B s
  let mult (s : ℝ) : StrongDual ℝ Corr := canonicalMultiplier (momD s) (objD s)
  have hstat : ∀ s ∈ Ioo A B,
      (∀ e : Corr, objD s ((0, 0), e) = mult s (momD s ((0, 0), e))) ∧
      objD s (((1, 0), 0)) = mult s (momD s (((1, 0), 0))) ∧
      objD s (((0, 1), 0)) ≤ mult s (momD s (((0, 1), 0))) := by
    intro s hs
    have hmax' : IsLocalMaxOn (splitIntegral (smoothG α) beta s)
        ({p | momentMap beta s p = momentMap beta s (baseParam c A B)} ∩
          {p | 0 ≤ p.1.2}) (baseParam c A B) :=
      isLocalMaxOn_of_inter_mem_nhds (splitDomain_mem_nhds_base c A B s hs)
        (hmax s hs)
    have hkkt := twoParameter_canonical_multiplier_stationarity
      (hasStrictFDerivAt_momentMap c beta A B s)
      (hasStrictFDerivAt_splitIntegral (smoothG α) (smoothG_continuous α)
        c beta A B s)
      (momentCorrectionBlock_isInvertible c beta A B s hAB hmass hmean hsecond)
      hmax'
    simpa [objD, momD, mult, baseParam] using hkkt
  have hmult : ∀ s ∈ Ioo A B, mult s = mult s0 := by
    intro s _
    exact canonicalMultiplier_moment_eq (smoothG α) (smoothG_continuous α)
      c beta A B s s0
  let L := mult s0
  let l0 := L (corrTriple 1 0 0)
  let l1 := L (corrTriple 0 1 0)
  let l2 := L (corrTriple 0 0 1)
  have hs := hstat s0 hs0
  have hcraw := hs.1 (corrTriple 1 0 0)
  have hbetaraw := hs.2.1
  have hAraw := hs.1 (corrTriple 0 1 0)
  have hBraw := hs.1 (corrTriple 0 0 1)
  have hc :
      (∫ x in A..B, smoothG α x * exponentialWeight c beta x) =
        l0 * (∫ x in A..B, exponentialWeight c beta x) +
        l1 * (∫ x in A..B, x * exponentialWeight c beta x) +
        l2 * (∫ x in A..B, x ^ 2 * exponentialWeight c beta x) := by
    change splitIntegralFDeriv (smoothG α) c beta A B s0 cDirection =
      L (momentFDeriv c beta A B s0 cDirection) at hcraw
    rw [splitIntegralFDeriv_cDirection (smoothG α) (smoothG_continuous α),
      momentFDeriv_cDirection, dual_corr_apply] at hcraw
    simpa [exponentialWeight, l0, l1, l2] using hcraw
  have hbeta :
      (∫ x in A..B, x * smoothG α x * exponentialWeight c beta x) =
        l0 * (∫ x in A..B, x * exponentialWeight c beta x) +
        l1 * (∫ x in A..B, x ^ 2 * exponentialWeight c beta x) +
        l2 * (∫ x in A..B, x ^ 3 * exponentialWeight c beta x) := by
    have hbdir : ((((1, 0), 0) : Param)) = betaDirection := by
      apply Prod.ext
      · rfl
      · funext i
        fin_cases i <;> simp [betaDirection, corrTriple]
    rw [hbdir] at hbetaraw
    change splitIntegralFDeriv (smoothG α) c beta A B s0 betaDirection =
      L (momentFDeriv c beta A B s0 betaDirection) at hbetaraw
    rw [splitIntegralFDeriv_betaDirection (smoothG α) (smoothG_continuous α),
      momentFDeriv_betaDirection, dual_corr_apply] at hbetaraw
    simpa [exponentialWeight, l0, l1, l2, mul_comm, mul_left_comm, mul_assoc,
      pow_succ] using hbetaraw
  have hAeq : smoothG α A = l0 + l1 * A + l2 * A ^ 2 := by
    change splitIntegralFDeriv (smoothG α) c beta A B s0 leftEndpointDirection =
      L (momentFDeriv c beta A B s0 leftEndpointDirection) at hAraw
    rw [splitIntegralFDeriv_leftEndpointDirection (smoothG α) (smoothG_continuous α),
      momentFDeriv_leftEndpointDirection, dual_corr_apply] at hAraw
    simp only [momentTest_zero, momentTest_one, momentTest_two] at hAraw
    apply mul_right_cancel₀ (Real.exp_ne_zero (c + beta * A))
    dsimp [l0, l1, l2]
    linear_combination -hAraw
  have hBeq : smoothG α B = l0 + l1 * B + l2 * B ^ 2 := by
    change splitIntegralFDeriv (smoothG α) c beta A B s0 rightEndpointDirection =
      L (momentFDeriv c beta A B s0 rightEndpointDirection) at hBraw
    rw [splitIntegralFDeriv_rightEndpointDirection (smoothG α) (smoothG_continuous α),
      momentFDeriv_rightEndpointDirection, dual_corr_apply] at hBraw
    simp only [momentTest_zero, momentTest_one, momentTest_two] at hBraw
    apply mul_right_cancel₀ (Real.exp_ne_zero (c + beta * B))
    dsimp [l0, l1, l2]
    linear_combination hBraw
  have hhinge : ∀ s ∈ Ioo A B,
      l0 * (∫ x in A..B, max (x - s) 0 * exponentialWeight c beta x) +
        l1 * (∫ x in A..B,
          max (x - s) 0 * x * exponentialWeight c beta x) +
        l2 * (∫ x in A..B,
          max (x - s) 0 * x ^ 2 * exponentialWeight c beta x) ≤
        ∫ x in A..B,
          max (x - s) 0 * smoothG α x * exponentialWeight c beta x := by
    intro s hsint
    have heta := (hstat s hsint).2.2
    rw [hmult s hsint] at heta
    have hedir : ((((0, 1), 0) : Param)) = etaDirection := by
      apply Prod.ext
      · rfl
      · funext i
        fin_cases i <;> simp [etaDirection, corrTriple]
    rw [hedir] at heta
    change splitIntegralFDeriv (smoothG α) c beta A B s etaDirection ≤
      L (momentFDeriv c beta A B s etaDirection) at heta
    rw [splitIntegralFDeriv_etaDirection (smoothG α) (smoothG_continuous α),
      momentFDeriv_etaDirection, dual_corr_apply] at heta
    simp only [momentTest_zero, momentTest_one, momentTest_two, mul_one] at heta
    have hsclosed : s ∈ Icc A B := ⟨hsint.1.le, hsint.2.le⟩
    have h0 := integral_max_sub_exp_eq_tail (fun _ : ℝ ↦ 1) continuous_const
      c beta hsclosed
    have h1 := integral_max_sub_exp_eq_tail (fun x : ℝ ↦ x) continuous_id
      c beta hsclosed
    have h2 := integral_max_sub_exp_eq_tail (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)
      c beta hsclosed
    have hg := integral_max_sub_exp_eq_tail (smoothG α) (smoothG_continuous α)
      c beta hsclosed
    simp only [mul_one] at h0
    simp only [exponentialWeight] at *
    rw [h0, h1, h2, hg]
    dsimp [l0, l1, l2]
    nlinarith
  let gamma := ∫ x in A..B,
    x ^ 2 * Real.exp (-α * |x|) * exponentialWeight c beta x
  exact no_compact_onePiece_of_stationarity_equations
    α gamma l0 l1 l2 c beta A B hα hAB
    (by simpa [exponentialWeight] using hmean)
    (by simpa [exponentialWeight] using hsecond)
    (by rfl)
    hc hbeta hAeq hBeq hhinge

/-- The same exclusion stated with the elementary objective
`(1 + α|x|) exp (-α|x|)` itself. -/
theorem no_compact_onePiece_localMax_explicitG
    (α c beta A B : ℝ) (hα : 0 < α) (hAB : A < B)
    (hmass : (∫ x in A..B, Real.exp (c + beta * x)) = 1)
    (hmean : (∫ x in A..B, x * Real.exp (c + beta * x)) = 0)
    (hsecond : (∫ x in A..B, x ^ 2 * Real.exp (c + beta * x)) = 1)
    (hmax : ∀ s ∈ Ioo A B,
      IsLocalMaxOn (splitIntegral (explicitG α) beta s)
        (splitDomain s ∩
          ({p | momentMap beta s p = momentMap beta s (baseParam c A B)} ∩
            {p | 0 ≤ p.1.2}))
        (baseParam c A B)) : False := by
  apply no_compact_onePiece_localMax α c beta A B hα hAB hmass hmean hsecond
  intro s hs
  have hmem : baseParam c A B ∈
      splitDomain s ∩
        ({p | momentMap beta s p = momentMap beta s (baseParam c A B)} ∩
          {p | 0 ≤ p.1.2}) := by
    refine ⟨?_, rfl, ?_⟩
    · simpa [splitDomain] using hs
    · simp [baseParam]
  apply (hmax s hs).congr
  · filter_upwards [] with p
    exact congrFun (splitIntegral_explicitG_eq_smoothG α beta s) p
  · exact hmem


end CompactOnePiece

/-! ## Flattened source: `lean_ii/ClaimIIFullFamilyBridge.lean` -/


open Filter Set MeasureTheory
open scoped Topology Interval

namespace CompactOnePiece

open LogConcaveExtremum
open LogConcaveExtremum.CompactSplitIntegral
open LogConcaveExtremum.CompactMomentMap


/-!
# Bridge from the compact part of family (6) to Claim (ii)

The six full-family coordinates are `(A,B,c,beta,delta,m)`.  The five split
coordinates used in Claim (ii) vary `beta`, `delta`, and the three correction
variables `(c,A,B)`, while keeping the kink `m=s` fixed.
-/

abbrev FullParam := LogConcaveClaimI.CompactParam

/-- The closed compact two-piece domain, including the one-piece boundary
`delta = 0`. -/
def compactClosedKinkDomain : Set FullParam :=
  {p | p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4}

/-- A one-piece density represented in the six-coordinate family with an
arbitrary redundant kink position `s`. -/
def onePieceFullParam (c beta A B s : ℝ) : FullParam :=
  ![A, B, c, beta, 0, s]

/-- Embed the fixed-kink split chart into the six-coordinate family. -/
def splitToFullParam (beta s : ℝ) (p : Param) : FullParam :=
  ![corrCLM 1 p, corrCLM 2 p, corrCLM 0 p,
    beta + betaCLM p, etaCLM p, s]

@[simp] lemma splitToFullParam_zero (beta s : ℝ) (p : Param) :
    splitToFullParam beta s p 0 = corrCLM 1 p := by
  simp [splitToFullParam]

@[simp] lemma splitToFullParam_one (beta s : ℝ) (p : Param) :
    splitToFullParam beta s p 1 = corrCLM 2 p := by
  simp [splitToFullParam]

@[simp] lemma splitToFullParam_two (beta s : ℝ) (p : Param) :
    splitToFullParam beta s p 2 = corrCLM 0 p := by
  simp [splitToFullParam]

@[simp] lemma splitToFullParam_three (beta s : ℝ) (p : Param) :
    splitToFullParam beta s p 3 = beta + betaCLM p := by
  simp [splitToFullParam]

@[simp] lemma splitToFullParam_four (beta s : ℝ) (p : Param) :
    splitToFullParam beta s p 4 = etaCLM p := by
  simp [splitToFullParam]

@[simp] lemma splitToFullParam_five (beta s : ℝ) (p : Param) :
    splitToFullParam beta s p 5 = s := by
  simp [splitToFullParam]

@[simp] lemma splitToFullParam_base (c beta A B s : ℝ) :
    splitToFullParam beta s (baseParam c A B) =
      onePieceFullParam c beta A B s := by
  funext i
  fin_cases i <;> simp [splitToFullParam, onePieceFullParam]

lemma continuous_splitToFullParam (beta s : ℝ) :
    Continuous (splitToFullParam beta s) := by
  rw [continuous_pi_iff]
  intro i
  fin_cases i <;> simp [splitToFullParam] <;> fun_prop

lemma fullLeftIntegrand_split (q : ℝ → ℝ) (beta s : ℝ)
    (p : Param) (x : ℝ) :
    LogConcaveClaimI.leftIntegrand q (splitToFullParam beta s p) x =
      CompactSplitIntegral.leftIntegrand q beta p x := by
  unfold LogConcaveClaimI.leftIntegrand LogConcaveClaimI.leftExponent
    CompactSplitIntegral.leftIntegrand
  simp only [splitToFullParam_two, splitToFullParam_three]
  congr 2
  simp [leftScore]
  ring

lemma fullRightIntegrand_split (q : ℝ → ℝ) (beta s : ℝ)
    (p : Param) (x : ℝ) :
    LogConcaveClaimI.rightIntegrand q (splitToFullParam beta s p) x =
      CompactSplitIntegral.rightIntegrand q beta s p x := by
  unfold LogConcaveClaimI.rightIntegrand LogConcaveClaimI.rightExponent
    CompactSplitIntegral.rightIntegrand
  simp only [splitToFullParam_two, splitToFullParam_three,
    splitToFullParam_four, splitToFullParam_five]
  congr 2
  simp [rightScore, leftScore]
  ring

/-- The split chart is literally the compact part of family (6). -/
theorem compactIntegral_splitToFullParam
    (q : ℝ → ℝ) (beta s : ℝ) (p : Param) :
    LogConcaveClaimI.compactIntegral q (splitToFullParam beta s p) =
      splitIntegral q beta s p := by
  unfold LogConcaveClaimI.compactIntegral LogConcaveClaimI.leftIntegral
    LogConcaveClaimI.rightIntegral splitIntegral
  simp only [splitToFullParam_zero, splitToFullParam_one,
    splitToFullParam_five]
  rw [intervalIntegral.integral_congr
      (fun x hx ↦ fullLeftIntegrand_split q beta s p x),
    intervalIntegral.integral_congr
      (fun x hx ↦ fullRightIntegrand_split q beta s p x)]

lemma momentTest_eq_pow (k : Fin 3) (x : ℝ) :
    momentTest k x = x ^ k.val := by
  fin_cases k
  · change 1 = x ^ 0
    simp
  · change x = x ^ 1
    simp
  · change x ^ 2 = x ^ 2
    rfl

/-- Mass, mean, and second moment agree under the chart embedding. -/
theorem compactMomentMap_splitToFullParam (beta s : ℝ) (p : Param) :
    LogConcaveClaimI.compactMomentMap (splitToFullParam beta s p) =
      momentMap beta s p := by
  funext k
  rw [LogConcaveClaimI.compactMomentMap, momentMap,
    compactIntegral_splitToFullParam]
  apply congrArg (fun q : ℝ → ℝ ↦ splitIntegral q beta s p)
  funext x
  exact (momentTest_eq_pow k x).symm

lemma onePieceFullParam_mem_domain
    {c beta A B s : ℝ} (hs : s ∈ Ioo A B) :
    onePieceFullParam c beta A B s ∈ compactClosedKinkDomain := by
  change A < s ∧ s < B ∧ (0 : ℝ) ≤ 0
  exact ⟨hs.1, hs.2, le_rfl⟩

lemma splitToFullParam_mem_domain
    {beta s : ℝ} {p : Param}
    (hp : p ∈ splitDomain s ∩ {p | 0 ≤ p.1.2}) :
    splitToFullParam beta s p ∈ compactClosedKinkDomain := by
  rcases hp with ⟨⟨hAs, hsB⟩, heta⟩
  exact ⟨hAs, hsB, heta⟩

/-- A one-piece representative has the same objective for every redundant
kink position. -/
theorem compactIntegral_onePieceFullParam
    (q : ℝ → ℝ) (hq : Continuous q)
    (c beta A B s : ℝ) :
    LogConcaveClaimI.compactIntegral q
        (onePieceFullParam c beta A B s) =
      ∫ x in A..B, q x * Real.exp (c + beta * x) := by
  rw [← splitToFullParam_base c beta A B s,
    compactIntegral_splitToFullParam,
    splitIntegral_base q hq]

theorem compactMomentMap_onePieceFullParam_independent
    (c beta A B s t : ℝ) :
    LogConcaveClaimI.compactMomentMap
        (onePieceFullParam c beta A B s) =
      LogConcaveClaimI.compactMomentMap
        (onePieceFullParam c beta A B t) := by
  funext k
  simp only [LogConcaveClaimI.compactMomentMap]
  rw [compactIntegral_onePieceFullParam (fun x : ℝ ↦ x ^ k.val)
      (continuous_id.pow k.val),
    compactIntegral_onePieceFullParam (fun x : ℝ ↦ x ^ k.val)
      (continuous_id.pow k.val)]

private lemma full_localMax_gives_split_localMax
    {alpha c beta A B s : ℝ} (hs : s ∈ Ioo A B)
    (hfull : IsLocalMaxOn
      (LogConcaveClaimI.compactIntegral (explicitG alpha))
      ({u | LogConcaveClaimI.compactMomentMap u =
          LogConcaveClaimI.compactMomentMap
            (onePieceFullParam c beta A B s)} ∩ compactClosedKinkDomain)
      (onePieceFullParam c beta A B s)) :
    IsLocalMaxOn (splitIntegral (explicitG alpha) beta s)
      (splitDomain s ∩
        ({p | momentMap beta s p = momentMap beta s (baseParam c A B)} ∩
          {p | 0 ≤ p.1.2}))
      (baseParam c A B) := by
  let S := splitDomain s ∩
    ({p | momentMap beta s p = momentMap beta s (baseParam c A B)} ∩
      {p | 0 ≤ p.1.2})
  let T := {u | LogConcaveClaimI.compactMomentMap u =
      LogConcaveClaimI.compactMomentMap
        (onePieceFullParam c beta A B s)} ∩ compactClosedKinkDomain
  have hsubset : S ⊆ splitToFullParam beta s ⁻¹' T := by
    intro p hp
    rcases hp with ⟨hdom, hmom, heta⟩
    constructor
    · change LogConcaveClaimI.compactMomentMap
          (splitToFullParam beta s p) =
        LogConcaveClaimI.compactMomentMap
          (onePieceFullParam c beta A B s)
      rw [compactMomentMap_splitToFullParam,
        ← splitToFullParam_base c beta A B s,
        compactMomentMap_splitToFullParam]
      exact hmom
    · exact splitToFullParam_mem_domain ⟨hdom, heta⟩
  have hcont : ContinuousOn (splitToFullParam beta s) S :=
    (continuous_splitToFullParam beta s).continuousOn
  have hbase : baseParam c A B ∈ S := by
    exact ⟨by simpa [splitDomain] using hs, rfl, by simp [baseParam]⟩
  have hfull' : IsLocalMaxOn
      (LogConcaveClaimI.compactIntegral (explicitG alpha)) T
      (splitToFullParam beta s (baseParam c A B)) := by
    simpa [T] using hfull
  have h := hfull'.comp_continuousOn (g := splitToFullParam beta s)
    hsubset hcont hbase
  simpa [S, T, Function.comp_def, compactIntegral_splitToFullParam] using h

/-- Local version of the bridge.  Because `m` is redundant when `delta=0`,
local maximality is required at every representative `m=s` of the same
one-piece density. -/
theorem no_compact_onePiece_localMax_fullFamily
    (alpha c beta A B : ℝ) (halpha : 0 < alpha) (hAB : A < B)
    (hmass : (∫ x in A..B, Real.exp (c + beta * x)) = 1)
    (hmean : (∫ x in A..B, x * Real.exp (c + beta * x)) = 0)
    (hsecond : (∫ x in A..B, x ^ 2 * Real.exp (c + beta * x)) = 1)
    (hlocal : ∀ s ∈ Ioo A B,
      IsLocalMaxOn
        (LogConcaveClaimI.compactIntegral (explicitG alpha))
        ({u | LogConcaveClaimI.compactMomentMap u =
            LogConcaveClaimI.compactMomentMap
              (onePieceFullParam c beta A B s)} ∩ compactClosedKinkDomain)
        (onePieceFullParam c beta A B s)) :
    False := by
  apply no_compact_onePiece_localMax_explicitG alpha c beta A B
    halpha hAB hmass hmean hsecond
  intro s hs
  exact full_localMax_gives_split_localMax hs (hlocal s hs)

/-- Global version needed for a maximizer in family (6).  A global maximum at
one redundant representative automatically gives the local hypothesis at
every representative, hence is impossible. -/
theorem no_compact_onePiece_globalMax_fullFamily
    (alpha c beta A B s0 : ℝ) (halpha : 0 < alpha) (hAB : A < B)
    (_hs0 : s0 ∈ Ioo A B)
    (hmass : (∫ x in A..B, Real.exp (c + beta * x)) = 1)
    (hmean : (∫ x in A..B, x * Real.exp (c + beta * x)) = 0)
    (hsecond : (∫ x in A..B, x ^ 2 * Real.exp (c + beta * x)) = 1)
    (hglobal : IsMaxOn
      (LogConcaveClaimI.compactIntegral (explicitG alpha))
      ({u | LogConcaveClaimI.compactMomentMap u =
          LogConcaveClaimI.compactMomentMap
            (onePieceFullParam c beta A B s0)} ∩ compactClosedKinkDomain)
      (onePieceFullParam c beta A B s0)) :
    False := by
  apply no_compact_onePiece_localMax_fullFamily alpha c beta A B
    halpha hAB hmass hmean hsecond
  intro s hs
  have hglobalS : IsMaxOn
      (LogConcaveClaimI.compactIntegral (explicitG alpha))
      ({u | LogConcaveClaimI.compactMomentMap u =
          LogConcaveClaimI.compactMomentMap
            (onePieceFullParam c beta A B s)} ∩ compactClosedKinkDomain)
      (onePieceFullParam c beta A B s) := by
    intro u hu
    have htarget := compactMomentMap_onePieceFullParam_independent
      c beta A B s s0
    have hu0 : u ∈
        ({v | LogConcaveClaimI.compactMomentMap v =
            LogConcaveClaimI.compactMomentMap
              (onePieceFullParam c beta A B s0)} ∩ compactClosedKinkDomain) := by
      exact ⟨hu.1.trans htarget, hu.2⟩
    have hle := hglobal hu0
    have hq : Continuous (explicitG alpha) :=
      continuous_iff_continuousAt.mpr
        (fun x ↦ (hasDerivAt_explicitG alpha x).continuousAt)
    change LogConcaveClaimI.compactIntegral (explicitG alpha) u ≤
      LogConcaveClaimI.compactIntegral (explicitG alpha)
        (onePieceFullParam c beta A B s) 
    change LogConcaveClaimI.compactIntegral (explicitG alpha) u ≤
      LogConcaveClaimI.compactIntegral (explicitG alpha)
        (onePieceFullParam c beta A B s0) at hle
    rw [compactIntegral_onePieceFullParam (explicitG alpha) hq c beta A B s0] at hle
    rw [compactIntegral_onePieceFullParam (explicitG alpha) hq c beta A B s]
    exact hle
  exact hglobalS.localize

end CompactOnePiece

/-! ## Kernel audit for the final exclusion theorems -/

end FlattenedExistenceSection1


/-!
Flattened source section: Family6TopLevel.lean
-/

section FlattenedExistenceSection2

/-!
# A top-level interface for family (6)

This file records the four possible support types of

`exp (c + beta*x - delta*(x-m)_+) * 1_[A,B](x)`

and isolates the short order-theoretic step which turns Claims (i)--(iii)
into a sharp maximum theorem.  The extra hypothesis `hattain` is deliberate:
Claims (i) and (ii) only exclude finite-endpoint *maximizers*.  By themselves
they do not prove that the supremum over the compactified family is attained.
-/


open Real Set MeasureTheory
open scoped Interval

namespace LogConcaveFamily6

open LogConcaveClaimI

/-- Parameters for the whole-line member of family (6). -/
structure WholeLineParam where
  c : ℝ
  beta : ℝ
  delta : ℝ
  m : ℝ

/-- The four possible support types in family (6).

For a finite-left (respectively finite-right) support, the existing
five-coordinate chart is `(A,c,beta,delta,m)` (respectively
`(B,c,beta,delta,m)`). -/
inductive Param where
  | compact (p : CompactParam)
  | finiteLeft (p : HalfLineParam)
  | finiteRight (p : HalfLineParam)
  | wholeLine (p : WholeLineParam)

/-- Integral of a test function against the density represented by a family
(6) parameter.  Endpoint values are immaterial for Lebesgue integration. -/
def integral (q : ℝ → ℝ) : Param → ℝ
  | .compact p => compactIntegral q p
  | .finiteLeft p => halfLineIntegral q p
  | .finiteRight p => finiteRightActualIntegral q p
  | .wholeLine p =>
      (∫ x in Iic p.m, q x * exp (p.c + p.beta * x)) +
        ∫ x in Ioi p.m,
          q x * exp (p.c + p.beta * x - p.delta * (x - p.m))

/-- The geometric and tail-integrability inequalities defining family (6).
Moment equalities are imposed separately by `IsIsotropic`. -/
def Admissible : Param → Prop
  | .compact p => p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4
  | .finiteLeft p => p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0
  | .finiteRight p => p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2
  | .wholeLine p => 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0

/-- The first three raw moments, with moment zero equal to total mass. -/
def momentMap (p : Param) (k : Fin 3) : ℝ :=
  integral (fun x ↦ x ^ k.val) p

/-- The mass/mean/second-moment vector `(1,0,1)`. -/
def isotropicTarget (k : Fin 3) : ℝ :=
  if k = 0 then 1 else if k = 1 then 0 else 1

/-- In this density model, isotropic means mass one, mean zero, and second
moment one. -/
def IsIsotropic (p : Param) : Prop :=
  momentMap p = isotropicTarget

/-- The isotropic part of family (6). -/
def family6 : Set Param :=
  {p | Admissible p ∧ IsIsotropic p}

/-- The objective in Theorem 2. -/
def objective (alpha : ℝ) (p : Param) : ℝ :=
  integral (gAlpha alpha) p

/-- Value at either centered one-sided exponential law.  This presentation is
regular at `alpha = 1`. -/
def S (alpha : ℝ) : ℝ :=
  exp (-1) *
    ((∫ x in (0 : ℝ)..1, (1 + alpha * x) * exp ((1 - alpha) * x)) +
      (1 + 2 * alpha) / (1 + alpha) ^ 2)

/-- Value at the isotropic symmetric Laplace law. -/
def L (alpha : ℝ) : ℝ :=
  2 * (1 + Real.sqrt 2 * alpha) / (Real.sqrt 2 + alpha) ^ 2

/-- Shapes ruled out by Claim (i): a genuine kink and at least one finite
support endpoint. -/
def ClaimIShape : Param → Prop
  | .compact p => 0 < p 4
  | .finiteLeft p => 0 < p 3
  | .finiteRight p => 0 < p 3
  | .wholeLine _ => False

/-- The shape ruled out by Claim (ii): a compact, one-piece log-affine
density. -/
def ClaimIIShape : Param → Prop
  | .compact p => p 4 = 0
  | _ => False

/-- The cases left for Claim (iii): a whole-line two-piece exponential or a
one-piece exponential on a half-line. -/
def TerminalShape : Param → Prop
  | .compact _ => False
  | .finiteLeft p => p 3 = 0
  | .finiteRight p => p 3 = 0
  | .wholeLine _ => True

/-- Every admissible family-(6) parameter belongs to exactly one of the three
classes relevant to Claims (i)--(iii).  Exclusivity is not needed below. -/
theorem shape_partition (p : Param) (hp : Admissible p) :
    ClaimIShape p ∨ ClaimIIShape p ∨ TerminalShape p := by
  cases p with
  | compact p =>
      change p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4 at hp
      rcases hp with ⟨_, _, hdelta⟩
      rcases hdelta.eq_or_lt with hzero | hpos
      · exact Or.inr (Or.inl hzero.symm)
      · exact Or.inl hpos
  | finiteLeft p =>
      change p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0 at hp
      rcases hp with ⟨_, hdelta, _⟩
      rcases hdelta.eq_or_lt with hzero | hpos
      · exact Or.inr (Or.inr hzero.symm)
      · exact Or.inl hpos
  | finiteRight p =>
      change p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2 at hp
      rcases hp with ⟨_, hdelta, _⟩
      rcases hdelta.eq_or_lt with hzero | hpos
      · exact Or.inr (Or.inr hzero.symm)
      · exact Or.inl hpos
  | wholeLine p =>
      exact Or.inr (Or.inr trivial)

/-! ## Bridges from the formalized Claims (i) and (ii) -/

/-- Claim (i), transported from its three parameter charts to the tagged
family: an attained global maximum cannot have a genuine kink together with
a finite support endpoint. -/
theorem no_claimIShape_globalMax
    {alpha : ℝ} (halpha : 0 < alpha) {theta : Param}
    (htheta : theta ∈ family6)
    (hmax : IsMaxOn (objective alpha) family6 theta)
    (hshape : ClaimIShape theta) : False := by
  rcases htheta with ⟨hadm, hiso⟩
  cases theta with
  | compact p =>
      change p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4 at hadm
      change 0 < p 4 at hshape
      have hpdom : p ∈ compactKinkDomain :=
        ⟨hadm.1, hadm.2.1, hshape⟩
      have hchart : IsMaxOn (compactIntegral (gAlpha alpha))
          ({u | compactMomentMap u = compactMomentMap p} ∩ compactKinkDomain) p := by
        intro u hu
        have huadm : Admissible (.compact u) := by
          change u 0 < u 5 ∧ u 5 < u 1 ∧ 0 ≤ u 4
          exact ⟨hu.2.1, hu.2.2.1, hu.2.2.2.le⟩
        have huiso : IsIsotropic (.compact u) := by
          change compactMomentMap u = isotropicTarget
          exact hu.1.trans hiso
        exact hmax ⟨huadm, huiso⟩
      exact no_compact_genuine_kink_local_extremum halpha hpdom
        (Or.inr hchart.localize)
  | finiteLeft p =>
      change p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0 at hadm
      change 0 < p 3 at hshape
      have hpdom : p ∈ finiteLeftKinkDomain :=
        ⟨hadm.1, hshape, hadm.2.2⟩
      have hchart : IsMaxOn (halfLineIntegral (gAlpha alpha))
          ({u | halfLineMomentMap u = halfLineMomentMap p} ∩
            finiteLeftKinkDomain) p := by
        intro u hu
        have huadm : Admissible (.finiteLeft u) := by
          change u 0 < u 4 ∧ 0 ≤ u 3 ∧ u 2 - u 3 < 0
          exact ⟨hu.2.1, hu.2.2.1.le, hu.2.2.2⟩
        have huiso : IsIsotropic (.finiteLeft u) := by
          change halfLineMomentMap u = isotropicTarget
          exact hu.1.trans hiso
        exact hmax ⟨huadm, huiso⟩
      exact no_finiteLeft_genuine_kink_local_extremum halpha hpdom
        (Or.inr hchart.localize)
  | finiteRight p =>
      change p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2 at hadm
      change 0 < p 3 at hshape
      have hpdom : p ∈ finiteRightKinkDomain :=
        ⟨hadm.1, hshape, hadm.2.2⟩
      have hchart : IsMaxOn (finiteRightActualIntegral (gAlpha alpha))
          ({u | finiteRightActualMomentMap u = finiteRightActualMomentMap p} ∩
            finiteRightKinkDomain) p := by
        intro u hu
        have huadm : Admissible (.finiteRight u) := by
          change u 4 < u 0 ∧ 0 ≤ u 3 ∧ 0 < u 2
          exact ⟨hu.2.1, hu.2.2.1.le, hu.2.2.2⟩
        have huiso : IsIsotropic (.finiteRight u) := by
          change finiteRightActualMomentMap u = isotropicTarget
          exact hu.1.trans hiso
        exact hmax ⟨huadm, huiso⟩
      exact no_finiteRight_genuine_kink_local_extremum halpha hpdom
        (Or.inr hchart.localize)
  | wholeLine p =>
      exact hshape

/-- Claim (ii), transported to the tagged family: an attained global maximum
cannot be a compact one-piece exponential. -/
theorem no_claimIIShape_globalMax
    {alpha : ℝ} (halpha : 0 < alpha) {theta : Param}
    (htheta : theta ∈ family6)
    (hmax : IsMaxOn (objective alpha) family6 theta)
    (hshape : ClaimIIShape theta) : False := by
  rcases htheta with ⟨hadm, hiso⟩
  cases theta with
  | compact p =>
      change p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4 at hadm
      change p 4 = 0 at hshape
      let p0 := CompactOnePiece.onePieceFullParam
        (p 2) (p 3) (p 0) (p 1) (p 5)
      have hp0 : p0 = p := by
        funext i
        fin_cases i <;> simp [p0, CompactOnePiece.onePieceFullParam, hshape]
      have hmass0 : compactIntegral (fun _ : ℝ ↦ 1) p = 1 := by
        have h := congrFun hiso (0 : Fin 3)
        simpa [momentMap, integral, isotropicTarget] using h
      have hmean0 : compactIntegral (fun x : ℝ ↦ x) p = 0 := by
        have h := congrFun hiso (1 : Fin 3)
        simpa [momentMap, integral, isotropicTarget] using h
      have hsecond0 : compactIntegral (fun x : ℝ ↦ x ^ 2) p = 1 := by
        have h := congrFun hiso (2 : Fin 3)
        simpa [momentMap, integral, isotropicTarget] using h
      have hmass :
          (∫ x in p 0..p 1, exp (p 2 + p 3 * x)) = 1 := by
        calc
          (∫ x in p 0..p 1, exp (p 2 + p 3 * x)) =
              compactIntegral (fun _ : ℝ ↦ 1) p0 := by
                symm
                simpa using
                  (CompactOnePiece.compactIntegral_onePieceFullParam
                    (fun _ : ℝ ↦ 1) continuous_const
                    (p 2) (p 3) (p 0) (p 1) (p 5))
          _ = compactIntegral (fun _ : ℝ ↦ 1) p := by rw [hp0]
          _ = 1 := hmass0
      have hmean :
          (∫ x in p 0..p 1, x * exp (p 2 + p 3 * x)) = 0 := by
        calc
          (∫ x in p 0..p 1, x * exp (p 2 + p 3 * x)) =
              compactIntegral (fun x : ℝ ↦ x) p0 := by
                symm
                exact CompactOnePiece.compactIntegral_onePieceFullParam
                  (fun x : ℝ ↦ x) continuous_id
                  (p 2) (p 3) (p 0) (p 1) (p 5)
          _ = compactIntegral (fun x : ℝ ↦ x) p := by rw [hp0]
          _ = 0 := hmean0
      have hsecond :
          (∫ x in p 0..p 1, x ^ 2 * exp (p 2 + p 3 * x)) = 1 := by
        calc
          (∫ x in p 0..p 1, x ^ 2 * exp (p 2 + p 3 * x)) =
              compactIntegral (fun x : ℝ ↦ x ^ 2) p0 := by
                symm
                exact CompactOnePiece.compactIntegral_onePieceFullParam
                  (fun x : ℝ ↦ x ^ 2) (continuous_id.pow 2)
                  (p 2) (p 3) (p 0) (p 1) (p 5)
          _ = compactIntegral (fun x : ℝ ↦ x ^ 2) p := by rw [hp0]
          _ = 1 := hsecond0
      have hchart : IsMaxOn
          (compactIntegral (CompactOnePiece.explicitG alpha))
          ({u | compactMomentMap u = compactMomentMap p0} ∩
            CompactOnePiece.compactClosedKinkDomain) p0 := by
        intro u hu
        have huadm : Admissible (.compact u) := by
          change u 0 < u 5 ∧ u 5 < u 1 ∧ 0 ≤ u 4
          exact hu.2
        have huiso : IsIsotropic (.compact u) := by
          change compactMomentMap u = isotropicTarget
          rw [hu.1, hp0]
          exact hiso
        have hle := hmax ⟨huadm, huiso⟩
        change compactIntegral (gAlpha alpha) u ≤
          compactIntegral (gAlpha alpha) p at hle
        change compactIntegral (CompactOnePiece.explicitG alpha) u ≤
          compactIntegral (CompactOnePiece.explicitG alpha) p0
        rw [hp0, show CompactOnePiece.explicitG alpha = gAlpha alpha from rfl]
        exact hle
      exact CompactOnePiece.no_compact_onePiece_globalMax_fullFamily
        alpha (p 2) (p 3) (p 0) (p 1) (p 5)
        halpha (hadm.1.trans hadm.2.1) (by exact ⟨hadm.1, hadm.2.1⟩)
        hmass hmean hsecond hchart
  | finiteLeft p =>
      exact hshape
  | finiteRight p =>
      exact hshape
  | wholeLine p =>
      exact hshape

/-- The classification that follows unconditionally from the formalized
Claims (i) and (ii): any *given attained global maximizer* in family (6) is a
one-piece half-line law or a whole-line asymmetric exponential law.  This
does not assert that such a global maximizer exists. -/
theorem globalMax_terminal
    {alpha : ℝ} (halpha : 0 < alpha) {theta : Param}
    (htheta : theta ∈ family6)
    (hmax : IsMaxOn (objective alpha) family6 theta) :
    TerminalShape theta := by
  rcases shape_partition theta htheta.1 with hI | hII | hIII
  · exact False.elim (no_claimIShape_globalMax halpha htheta hmax hI)
  · exact False.elim (no_claimIIShape_globalMax halpha htheta hmax hII)
  · exact hIII

/-- The same classification with the support alternatives made explicit. -/
theorem globalMax_is_oneSided_or_wholeLine
    {alpha : ℝ} (halpha : 0 < alpha) {theta : Param}
    (htheta : theta ∈ family6)
    (hmax : IsMaxOn (objective alpha) family6 theta) :
    (∃ p : HalfLineParam, theta = .finiteLeft p ∧ p 3 = 0) ∨
      (∃ p : HalfLineParam, theta = .finiteRight p ∧ p 3 = 0) ∨
      ∃ p : WholeLineParam, theta = .wholeLine p := by
  have hterminal := globalMax_terminal halpha htheta hmax
  cases theta with
  | compact p => exact hterminal.elim
  | finiteLeft p => exact Or.inl ⟨p, rfl, hterminal⟩
  | finiteRight p => exact Or.inr (Or.inl ⟨p, rfl, hterminal⟩)
  | wholeLine p => exact Or.inr (Or.inr ⟨p, rfl⟩)

/-- The precise logical bridge from Claims (i)--(iii) to the pointwise upper
bound.  Notice that Claims (i) and (ii) are used only at an attained global
maximum. -/
theorem objective_le_max_of_claims
    (alpha : ℝ)
    (hattain : ∃ q ∈ family6,
      IsMaxOn (objective alpha) family6 q)
    (hclaimI : ∀ q ∈ family6,
      IsMaxOn (objective alpha) family6 q → ClaimIShape q → False)
    (hclaimII : ∀ q ∈ family6,
      IsMaxOn (objective alpha) family6 q → ClaimIIShape q → False)
    (hclaimIII : ∀ q ∈ family6, TerminalShape q →
      objective alpha q ≤ max (S alpha) (L alpha)) :
    ∀ p ∈ family6, objective alpha p ≤ max (S alpha) (L alpha) := by
  rintro p hp
  obtain ⟨q, hq, hqmax⟩ := hattain
  have hterminal : TerminalShape q := by
    rcases shape_partition q hq.1 with hI | hII | hIII
    · exact False.elim (hclaimI q hq hqmax hI)
    · exact False.elim (hclaimII q hq hqmax hII)
    · exact hIII
  exact (hqmax hp).trans (hclaimIII q hq hterminal)

/-- Sharp version of the preceding bridge.  The two witness assumptions are
the elementary evaluations at the centered one-sided exponential and at the
isotropic symmetric Laplace density. -/
theorem family6_isGreatest_of_claims
    (alpha : ℝ)
    (hattain : ∃ q ∈ family6,
      IsMaxOn (objective alpha) family6 q)
    (hclaimI : ∀ q ∈ family6,
      IsMaxOn (objective alpha) family6 q → ClaimIShape q → False)
    (hclaimII : ∀ q ∈ family6,
      IsMaxOn (objective alpha) family6 q → ClaimIIShape q → False)
    (hclaimIII : ∀ q ∈ family6, TerminalShape q →
      objective alpha q ≤ max (S alpha) (L alpha))
    (hS : ∃ p ∈ family6, objective alpha p = S alpha)
    (hL : ∃ p ∈ family6, objective alpha p = L alpha) :
    IsGreatest (objective alpha '' family6) (max (S alpha) (L alpha)) := by
  constructor
  · rcases le_total (S alpha) (L alpha) with hSL | hLS
    · rw [max_eq_right hSL]
      obtain ⟨p, hp, hpL⟩ := hL
      exact ⟨p, hp, hpL⟩
    · rw [max_eq_left hLS]
      obtain ⟨p, hp, hpS⟩ := hS
      exact ⟨p, hp, hpS⟩
  · rintro y ⟨p, hp, rfl⟩
    exact objective_le_max_of_claims alpha hattain hclaimI hclaimII hclaimIII p hp

/-- Pointwise bound after discharging the Claim-(i) and Claim-(ii) hypotheses
with the formalized exclusion theorems.  The two remaining assumptions are
displayed explicitly: attainment in the extended family and the terminal
Claim-(iii) estimate. -/
theorem objective_le_max_of_attainment_and_claimIII
    {alpha : ℝ} (halpha : 0 < alpha)
    (hattain : ∃ q ∈ family6,
      IsMaxOn (objective alpha) family6 q)
    (hclaimIII : ∀ q ∈ family6, TerminalShape q →
      objective alpha q ≤ max (S alpha) (L alpha)) :
    ∀ p ∈ family6, objective alpha p ≤ max (S alpha) (L alpha) := by
  exact objective_le_max_of_claims alpha hattain
    (fun q hq hqmax hI ↦ no_claimIShape_globalMax halpha hq hqmax hI)
    (fun q hq hqmax hII ↦ no_claimIIShape_globalMax halpha hq hqmax hII)
    hclaimIII

/-- Sharp maximum theorem with all still-unformalized ingredients exposed as
hypotheses.  In particular, `hattain` is the missing compactification theorem;
it is not a consequence of Claims (i) and (ii). -/
theorem family6_isGreatest_of_attainment_and_claimIII
    {alpha : ℝ} (halpha : 0 < alpha)
    (hattain : ∃ q ∈ family6,
      IsMaxOn (objective alpha) family6 q)
    (hclaimIII : ∀ q ∈ family6, TerminalShape q →
      objective alpha q ≤ max (S alpha) (L alpha))
    (hS : ∃ p ∈ family6, objective alpha p = S alpha)
    (hL : ∃ p ∈ family6, objective alpha p = L alpha) :
    IsGreatest (objective alpha '' family6) (max (S alpha) (L alpha)) := by
  exact family6_isGreatest_of_claims alpha hattain
    (fun q hq hqmax hI ↦ no_claimIShape_globalMax halpha hq hqmax hI)
    (fun q hq hqmax hII ↦ no_claimIIShape_globalMax halpha hq hqmax hII)
    hclaimIII hS hL

end LogConcaveFamily6

end FlattenedExistenceSection2


/-!
Flattened source section: Family6Law.lean
-/

section FlattenedExistenceSection3

open Real Set MeasureTheory
open scoped ENNReal Interval

namespace LogConcaveFamily6.Law

open LogConcaveClaimI

/-- The ordinary Lebesgue density represented by a tagged family-(6)
parameter.  The half-open endpoint conventions make the two pieces disjoint;
they are immaterial for integration. -/
def realDensity : LogConcaveFamily6.Param → ℝ → ℝ
  | .compact p => fun x ↦
      (Ioc (p 0) (p 5)).indicator (fun y ↦ exp (leftExponent p y)) x +
        (Ioc (p 5) (p 1)).indicator (fun y ↦ exp (rightExponent p y)) x
  | .finiteLeft p => fun x ↦
      (Ioc (p 0) (p 4)).indicator (fun y ↦ exp (halfLineLeftExponent p y)) x +
        (Ioi (p 4)).indicator (fun y ↦ exp (halfLineRightExponent p y)) x
  | .finiteRight p => fun x ↦
      (Iic (p 4)).indicator (fun y ↦ exp (finiteRightLeftExponent p y)) x +
        (Ioc (p 4) (p 0)).indicator
          (fun y ↦ exp (finiteRightRightExponent p y)) x
  | .wholeLine p => fun x ↦
      (Iic p.m).indicator (fun y ↦ exp (p.c + p.beta * y)) x +
        (Ioi p.m).indicator
          (fun y ↦ exp (p.c + p.beta * y - p.delta * (y - p.m))) x

theorem realDensity_nonneg (p : LogConcaveFamily6.Param) (x : ℝ) :
    0 ≤ realDensity p x := by
  cases p <;> simp only [realDensity] <;>
    exact add_nonneg (indicator_nonneg (fun _ _ ↦ (exp_pos _).le) _)
      (indicator_nonneg (fun _ _ ↦ (exp_pos _).le) _)

theorem measurable_realDensity (p : LogConcaveFamily6.Param) :
    Measurable (realDensity p) := by
  cases p with
  | compact p =>
      exact ((continuous_compactLeftWeight p).measurable.indicator measurableSet_Ioc).add
        ((continuous_compactRightWeight p).measurable.indicator measurableSet_Ioc)
  | finiteLeft p =>
      exact ((continuous_finiteLeftWeight p).measurable.indicator measurableSet_Ioc).add
        ((continuous_finiteRightTailWeight p).measurable.indicator measurableSet_Ioi)
  | finiteRight p =>
      exact (show Measurable (fun y : ℝ ↦ exp (finiteRightLeftExponent p y)) by
          unfold finiteRightLeftExponent
          fun_prop).indicator measurableSet_Iic |>.add
        ((show Measurable (fun y : ℝ ↦ exp (finiteRightRightExponent p y)) by
          unfold finiteRightRightExponent
          fun_prop).indicator measurableSet_Ioc)
  | wholeLine p =>
      apply Measurable.add
      · exact (by fun_prop : Measurable (fun y : ℝ ↦ exp (p.c + p.beta * y))).indicator
          measurableSet_Iic
      · exact (by fun_prop : Measurable (fun y : ℝ ↦
          exp (p.c + p.beta * y - p.delta * (y - p.m)))).indicator measurableSet_Ioi

/-- The measure with the displayed family-(6) density. -/
def rawMeasure (p : LogConcaveFamily6.Param) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (realDensity p x))

theorem integral_rawMeasure (p : LogConcaveFamily6.Param) (q : ℝ → ℝ) :
    (∫ x, q x ∂rawMeasure p) = ∫ x, realDensity p x * q x := by
  rw [rawMeasure,
    integral_withDensity_eq_integral_toReal_smul
      ((measurable_realDensity p).ennreal_ofReal) (by simp)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (realDensity_nonneg p x)]
  simp [smul_eq_mul, mul_comm]

/-- Integrability of a test function against each of the two density pieces.
It is kept separate from `integral_against_density` so that polynomial and
`gAlpha` tail bounds can be supplied by the existing specialized lemmas. -/
def PieceIntegrable (p : LogConcaveFamily6.Param) (q : ℝ → ℝ) : Prop :=
  match p with
  | .compact u =>
      IntegrableOn (fun x ↦ q x * exp (leftExponent u x)) (Ioc (u 0) (u 5)) ∧
      IntegrableOn (fun x ↦ q x * exp (rightExponent u x)) (Ioc (u 5) (u 1))
  | .finiteLeft u =>
      IntegrableOn (fun x ↦ q x * exp (halfLineLeftExponent u x))
          (Ioc (u 0) (u 4)) ∧
      IntegrableOn (fun x ↦ q x * exp (halfLineRightExponent u x)) (Ioi (u 4))
  | .finiteRight u =>
      IntegrableOn (fun x ↦ q x * exp (finiteRightLeftExponent u x)) (Iic (u 4)) ∧
      IntegrableOn (fun x ↦ q x * exp (finiteRightRightExponent u x))
        (Ioc (u 4) (u 0))
  | .wholeLine u =>
      IntegrableOn (fun x ↦ q x * exp (u.c + u.beta * x)) (Iic u.m) ∧
      IntegrableOn
        (fun x ↦ q x * exp (u.c + u.beta * x - u.delta * (x - u.m))) (Ioi u.m)

/-- The tagged integral is the ordinary Lebesgue integral against
`realDensity`. -/
theorem integral_against_realDensity
    {p : LogConcaveFamily6.Param} (hp : LogConcaveFamily6.Admissible p)
    (q : ℝ → ℝ) (hq : PieceIntegrable p q) :
    (∫ x, realDensity p x * q x) = LogConcaveFamily6.integral q p := by
  cases p with
  | compact u =>
      change u 0 < u 5 ∧ u 5 < u 1 ∧ 0 ≤ u 4 at hp
      change _ ∧ _ at hq
      have hfun : (fun x : ℝ ↦ realDensity (.compact u) x * q x) =
          (fun x ↦
            (Ioc (u 0) (u 5)).indicator
                (fun y ↦ q y * exp (leftExponent u y)) x +
              (Ioc (u 5) (u 1)).indicator
                (fun y ↦ q y * exp (rightExponent u y)) x) := by
        funext x
        by_cases hL : x ∈ Ioc (u 0) (u 5) <;>
          by_cases hR : x ∈ Ioc (u 5) (u 1) <;>
          simp [realDensity, hL, hR] <;> ring
      rw [hfun, integral_add
        (hq.1.integrable_indicator measurableSet_Ioc)
        (hq.2.integrable_indicator measurableSet_Ioc),
        integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le hp.1.le,
        ← intervalIntegral.integral_of_le hp.2.1.le]
      rfl
  | finiteLeft u =>
      change u 0 < u 4 ∧ 0 ≤ u 3 ∧ u 2 - u 3 < 0 at hp
      change _ ∧ _ at hq
      have hfun : (fun x : ℝ ↦ realDensity (.finiteLeft u) x * q x) =
          (fun x ↦
            (Ioc (u 0) (u 4)).indicator
                (fun y ↦ q y * exp (halfLineLeftExponent u y)) x +
              (Ioi (u 4)).indicator
                (fun y ↦ q y * exp (halfLineRightExponent u y)) x) := by
        funext x
        by_cases hL : x ∈ Ioc (u 0) (u 4) <;>
          by_cases hR : x ∈ Ioi (u 4) <;>
          simp [realDensity, hL, hR] <;> ring
      rw [hfun, integral_add
        (hq.1.integrable_indicator measurableSet_Ioc)
        (hq.2.integrable_indicator measurableSet_Ioi),
        integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioi,
        ← intervalIntegral.integral_of_le hp.1.le]
      rfl
  | finiteRight u =>
      change u 4 < u 0 ∧ 0 ≤ u 3 ∧ 0 < u 2 at hp
      change _ ∧ _ at hq
      have hfun : (fun x : ℝ ↦ realDensity (.finiteRight u) x * q x) =
          (fun x ↦
            (Iic (u 4)).indicator
                (fun y ↦ q y * exp (finiteRightLeftExponent u y)) x +
              (Ioc (u 4) (u 0)).indicator
                (fun y ↦ q y * exp (finiteRightRightExponent u y)) x) := by
        funext x
        by_cases hL : x ∈ Iic (u 4) <;>
          by_cases hR : x ∈ Ioc (u 4) (u 0) <;>
          simp [realDensity, hL, hR] <;> ring
      rw [hfun, integral_add
        (hq.1.integrable_indicator measurableSet_Iic)
        (hq.2.integrable_indicator measurableSet_Ioc),
        integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le hp.1.le]
      rfl
  | wholeLine u =>
      change 0 ≤ u.delta ∧ 0 < u.beta ∧ u.beta - u.delta < 0 at hp
      change _ ∧ _ at hq
      have hfun : (fun x : ℝ ↦ realDensity (.wholeLine u) x * q x) =
          (fun x ↦
            (Iic u.m).indicator (fun y ↦ q y * exp (u.c + u.beta * y)) x +
              (Ioi u.m).indicator
                (fun y ↦ q y * exp
                  (u.c + u.beta * y - u.delta * (y - u.m))) x) := by
        funext x
        by_cases hL : x ∈ Iic u.m <;> by_cases hR : x ∈ Ioi u.m <;>
          simp [realDensity, hL, hR] <;> ring
      rw [hfun, integral_add
        (hq.1.integrable_indicator measurableSet_Iic)
        (hq.2.integrable_indicator measurableSet_Ioi),
        integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ioi]
      rfl

/-- Piecewise integrability is exactly what is needed for integrability
against the full displayed density. -/
theorem integrable_realDensity_mul
    {p : LogConcaveFamily6.Param} {q : ℝ → ℝ}
    (hq : PieceIntegrable p q) :
    Integrable (fun x ↦ realDensity p x * q x) := by
  cases p with
  | compact u =>
      change _ ∧ _ at hq
      have h := (hq.1.integrable_indicator measurableSet_Ioc).add
        (hq.2.integrable_indicator measurableSet_Ioc)
      apply h.congr
      filter_upwards [] with x
      by_cases hL : x ∈ Ioc (u 0) (u 5) <;>
        by_cases hR : x ∈ Ioc (u 5) (u 1) <;>
        simp [realDensity, hL, hR] <;> ring
  | finiteLeft u =>
      change _ ∧ _ at hq
      have h := (hq.1.integrable_indicator measurableSet_Ioc).add
        (hq.2.integrable_indicator measurableSet_Ioi)
      apply h.congr
      filter_upwards [] with x
      by_cases hL : x ∈ Ioc (u 0) (u 4) <;>
        by_cases hR : x ∈ Ioi (u 4) <;>
        simp [realDensity, hL, hR] <;> ring
  | finiteRight u =>
      change _ ∧ _ at hq
      have h := (hq.1.integrable_indicator measurableSet_Iic).add
        (hq.2.integrable_indicator measurableSet_Ioc)
      apply h.congr
      filter_upwards [] with x
      by_cases hL : x ∈ Iic (u 4) <;>
        by_cases hR : x ∈ Ioc (u 4) (u 0) <;>
        simp [realDensity, hL, hR] <;> ring
  | wholeLine u =>
      change _ ∧ _ at hq
      have h := (hq.1.integrable_indicator measurableSet_Iic).add
        (hq.2.integrable_indicator measurableSet_Ioi)
      apply h.congr
      filter_upwards [] with x
      by_cases hL : x ∈ Iic u.m <;> by_cases hR : x ∈ Ioi u.m <;>
        simp [realDensity, hL, hR] <;> ring

theorem integrable_rawMeasure_of_piece
    {p : LogConcaveFamily6.Param} {q : ℝ → ℝ}
    (hq : PieceIntegrable p q) : Integrable q (rawMeasure p) := by
  rw [rawMeasure, integrable_withDensity_iff
    ((measurable_realDensity p).ennreal_ofReal) (by simp)]
  have h := integrable_realDensity_mul hq
  apply h.congr
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (realDensity_nonneg p x)]
  ring

/-- The same identity for the measure-valued representation. -/
theorem integral_rawMeasure_eq_tagged
    {p : LogConcaveFamily6.Param} (hp : LogConcaveFamily6.Admissible p)
    (q : ℝ → ℝ) (hq : PieceIntegrable p q) :
    (∫ x, q x ∂rawMeasure p) = LogConcaveFamily6.integral q p := by
  rw [integral_rawMeasure]
  exact integral_against_realDensity hp q hq

private theorem integrableOn_pow_mul_exp_affine_Ioi
    (n : ℕ) (c k a : ℝ) (hk : k < 0) :
    IntegrableOn (fun x : ℝ ↦ x ^ n * exp (c + k * x)) (Ioi a) := by
  have h : IntegrableOn
      (fun x : ℝ ↦ exp c * (x ^ n * exp (k * x))) (Ioi a) :=
    (integrableOn_pow_mul_exp_mul_Ioi n hk a).const_mul (exp c)
  apply h.congr_fun_ae
  filter_upwards [] with x
  rw [exp_add]
  ring

private theorem integrableOn_pow_mul_exp_affine_Iic
    (n : ℕ) (c k a : ℝ) (hk : 0 < k) :
    IntegrableOn (fun x : ℝ ↦ x ^ n * exp (c + k * x)) (Iic a) := by
  rw [integrableOn_Iic_iff_integrableOn_Iio]
  have h : IntegrableOn
      (fun x : ℝ ↦ exp c * (x ^ n * exp (k * x))) (Iio a) :=
    (integrableOn_pow_mul_exp_mul_Iio n hk a).const_mul (exp c)
  apply h.congr_fun_ae
  filter_upwards [] with x
  rw [exp_add]
  ring

private theorem integrableOn_pow_mul_gAlpha_exp_affine_Ioi
    (n : ℕ) (alpha c k a : ℝ) (halpha : 0 ≤ alpha) (hk : k < 0) :
    IntegrableOn
      (fun x : ℝ ↦ x ^ n * gAlpha alpha x * exp (c + k * x)) (Ioi a) := by
  have h : IntegrableOn
      (fun x : ℝ ↦ exp c *
        (x ^ n * gAlpha alpha x * exp (k * x))) (Ioi a) :=
    (integrableOn_pow_mul_gAlpha_mul_exp_mul_Ioi n halpha hk a).const_mul (exp c)
  apply h.congr_fun_ae
  filter_upwards [] with x
  rw [exp_add]
  ring

private theorem integrableOn_pow_mul_gAlpha_exp_affine_Iic
    (n : ℕ) (alpha c k a : ℝ) (halpha : 0 ≤ alpha) (hk : 0 < k) :
    IntegrableOn
      (fun x : ℝ ↦ x ^ n * gAlpha alpha x * exp (c + k * x)) (Iic a) := by
  rw [integrableOn_Iic_iff_integrableOn_Iio]
  have h : IntegrableOn
      (fun x : ℝ ↦ exp c *
        (x ^ n * gAlpha alpha x * exp (k * x))) (Iio a) :=
    (integrableOn_pow_mul_gAlpha_mul_exp_mul_Iio n halpha hk a).const_mul (exp c)
  apply h.congr_fun_ae
  filter_upwards [] with x
  rw [exp_add]
  ring

private theorem compactPiece_integrable
    {q w : ℝ → ℝ} (hq : Continuous q) (hw : Continuous w) (a b : ℝ) :
    IntegrableOn (fun x ↦ q x * w x) (Ioc a b) :=
  (hq.mul hw).integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- Every polynomial moment is integrable on both pieces of an admissible
family-(6) density. -/
theorem pieceIntegrable_pow (n : ℕ) {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.Admissible p) :
    PieceIntegrable p (fun x : ℝ ↦ x ^ n) := by
  cases p with
  | compact u =>
      exact ⟨compactPiece_integrable (continuous_id.pow n)
          (continuous_compactLeftWeight u) _ _,
        compactPiece_integrable (continuous_id.pow n)
          (continuous_compactRightWeight u) _ _⟩
  | finiteLeft u =>
      change u 0 < u 4 ∧ 0 ≤ u 3 ∧ u 2 - u 3 < 0 at hp
      exact ⟨compactPiece_integrable (continuous_id.pow n)
          (continuous_finiteLeftWeight u) _ _,
        by simpa [finiteRightTailWeight] using
          integrableOn_pow_mul_finiteRightTailWeight u n hp.2.2 (u 4)⟩
  | finiteRight u =>
      change u 4 < u 0 ∧ 0 ≤ u 3 ∧ 0 < u 2 at hp
      exact ⟨by simpa only [finiteRightLeftExponent] using
          integrableOn_pow_mul_exp_affine_Iic n (u 1) (u 2) (u 4) hp.2.2,
        compactPiece_integrable (continuous_id.pow n)
          (show Continuous (fun x : ℝ ↦ exp (finiteRightRightExponent u x)) by
            unfold finiteRightRightExponent
            fun_prop) _ _⟩
  | wholeLine u =>
      change 0 ≤ u.delta ∧ 0 < u.beta ∧ u.beta - u.delta < 0 at hp
      constructor
      · exact integrableOn_pow_mul_exp_affine_Iic n u.c u.beta u.m hp.2.1
      · have h := integrableOn_pow_mul_exp_affine_Ioi n
          (u.c + u.delta * u.m) (u.beta - u.delta) u.m hp.2.2
        apply h.congr_fun_ae
        filter_upwards [] with x
        congr 2
        ring

/-- Mass is integrable on both density pieces. -/
theorem pieceIntegrable_one {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.Admissible p) :
    PieceIntegrable p (fun _ : ℝ ↦ 1) := by
  cases p with
  | compact u =>
      exact ⟨compactPiece_integrable continuous_const
          (continuous_compactLeftWeight u) _ _,
        compactPiece_integrable continuous_const
          (continuous_compactRightWeight u) _ _⟩
  | finiteLeft u =>
      change u 0 < u 4 ∧ 0 ≤ u 3 ∧ u 2 - u 3 < 0 at hp
      constructor
      · exact compactPiece_integrable continuous_const
          (continuous_finiteLeftWeight u) _ _
      · simpa [finiteRightTailWeight] using
          integrableOn_pow_mul_finiteRightTailWeight u 0 hp.2.2 (u 4)
  | finiteRight u =>
      change u 4 < u 0 ∧ 0 ≤ u 3 ∧ 0 < u 2 at hp
      constructor
      · simpa only [finiteRightLeftExponent, pow_zero, one_mul] using
          integrableOn_pow_mul_exp_affine_Iic 0 (u 1) (u 2) (u 4) hp.2.2
      · exact compactPiece_integrable continuous_const
          (show Continuous (fun x : ℝ ↦ exp (finiteRightRightExponent u x)) by
            unfold finiteRightRightExponent
            fun_prop) _ _
  | wholeLine u =>
      change 0 ≤ u.delta ∧ 0 < u.beta ∧ u.beta - u.delta < 0 at hp
      constructor
      · simpa only [pow_zero, one_mul] using
          integrableOn_pow_mul_exp_affine_Iic 0 u.c u.beta u.m hp.2.1
      · have h := integrableOn_pow_mul_exp_affine_Ioi 0
          (u.c + u.delta * u.m) (u.beta - u.delta) u.m hp.2.2
        apply h.congr_fun_ae
        filter_upwards [] with x
        simp only [pow_zero, one_mul]
        congr 1
        ring

/-- The second moment is integrable on both density pieces. -/
theorem pieceIntegrable_sq {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.Admissible p) :
    PieceIntegrable p (fun x : ℝ ↦ x ^ 2) := by
  cases p with
  | compact u =>
      exact ⟨compactPiece_integrable (continuous_id.pow 2)
          (continuous_compactLeftWeight u) _ _,
        compactPiece_integrable (continuous_id.pow 2)
          (continuous_compactRightWeight u) _ _⟩
  | finiteLeft u =>
      change u 0 < u 4 ∧ 0 ≤ u 3 ∧ u 2 - u 3 < 0 at hp
      exact ⟨compactPiece_integrable (continuous_id.pow 2)
          (continuous_finiteLeftWeight u) _ _,
        by simpa [finiteRightTailWeight] using
          integrableOn_pow_mul_finiteRightTailWeight u 2 hp.2.2 (u 4)⟩
  | finiteRight u =>
      change u 4 < u 0 ∧ 0 ≤ u 3 ∧ 0 < u 2 at hp
      exact ⟨integrableOn_pow_mul_exp_affine_Iic 2 (u 1) (u 2) (u 4) hp.2.2,
        compactPiece_integrable (continuous_id.pow 2)
          (show Continuous (fun x : ℝ ↦ exp (finiteRightRightExponent u x)) by
            unfold finiteRightRightExponent
            fun_prop) _ _⟩
  | wholeLine u =>
      change 0 ≤ u.delta ∧ 0 < u.beta ∧ u.beta - u.delta < 0 at hp
      constructor
      · exact integrableOn_pow_mul_exp_affine_Iic 2 u.c u.beta u.m hp.2.1
      · have h := integrableOn_pow_mul_exp_affine_Ioi 2
          (u.c + u.delta * u.m) (u.beta - u.delta) u.m hp.2.2
        apply h.congr_fun_ae
        filter_upwards [] with x
        congr 2
        ring

/-- The bounded `gAlpha` objective is integrable on both density pieces. -/
theorem pieceIntegrable_gAlpha {alpha : ℝ} (halpha : 0 ≤ alpha)
    {p : LogConcaveFamily6.Param} (hp : LogConcaveFamily6.Admissible p) :
    PieceIntegrable p (gAlpha alpha) := by
  cases p with
  | compact u =>
      exact ⟨compactPiece_integrable (continuous_gAlpha alpha)
          (continuous_compactLeftWeight u) _ _,
        compactPiece_integrable (continuous_gAlpha alpha)
          (continuous_compactRightWeight u) _ _⟩
  | finiteLeft u =>
      change u 0 < u 4 ∧ 0 ≤ u 3 ∧ u 2 - u 3 < 0 at hp
      exact ⟨compactPiece_integrable (continuous_gAlpha alpha)
          (continuous_finiteLeftWeight u) _ _,
        by simpa [finiteRightTailWeight] using
          integrableOn_gAlpha_mul_finiteRightTailWeight halpha u hp.2.2 (u 4)⟩
  | finiteRight u =>
      change u 4 < u 0 ∧ 0 ≤ u 3 ∧ 0 < u 2 at hp
      constructor
      · simpa only [finiteRightLeftExponent, pow_zero, one_mul] using
          integrableOn_pow_mul_gAlpha_exp_affine_Iic 0 alpha
            (u 1) (u 2) (u 4) halpha hp.2.2
      · exact compactPiece_integrable (continuous_gAlpha alpha)
          (show Continuous (fun x : ℝ ↦ exp (finiteRightRightExponent u x)) by
            unfold finiteRightRightExponent
            fun_prop) _ _
  | wholeLine u =>
      change 0 ≤ u.delta ∧ 0 < u.beta ∧ u.beta - u.delta < 0 at hp
      constructor
      · simpa only [pow_zero, one_mul] using
          integrableOn_pow_mul_gAlpha_exp_affine_Iic 0 alpha
            u.c u.beta u.m halpha hp.2.1
      · have h := integrableOn_pow_mul_gAlpha_exp_affine_Ioi 0 alpha
          (u.c + u.delta * u.m) (u.beta - u.delta) u.m halpha hp.2.2
        apply h.congr_fun_ae
        filter_upwards [] with x
        simp only [pow_zero, one_mul]
        congr 2
        ring

theorem tagged_moment_eq_target {p : LogConcaveFamily6.Param}
    (hp : p ∈ LogConcaveFamily6.family6) (k : Fin 3) :
    LogConcaveFamily6.integral (fun x : ℝ ↦ x ^ k.val) p =
      LogConcaveFamily6.isotropicTarget k := by
  exact congrFun hp.2 k

theorem rawMeasure_real_univ {p : LogConcaveFamily6.Param}
    (hp : p ∈ LogConcaveFamily6.family6) :
    (rawMeasure p).real univ = 1 := by
  have h := integral_rawMeasure_eq_tagged hp.1 (fun _ : ℝ ↦ 1)
    (pieceIntegrable_one hp.1)
  simp only [integral_const, smul_eq_mul, mul_one] at h
  have hmass := tagged_moment_eq_target hp (0 : Fin 3)
  simpa [LogConcaveFamily6.isotropicTarget] using h.trans hmass

/-- The probability law represented by an isotropic tagged family-(6)
parameter. -/
def law (p : LogConcaveFamily6.Param)
    (hp : p ∈ LogConcaveFamily6.family6) : ProbabilityMeasure ℝ :=
  ⟨rawMeasure p, isProbabilityMeasure_iff_real.2 (rawMeasure_real_univ hp)⟩

@[simp] theorem law_toMeasure (p : LogConcaveFamily6.Param)
    (hp : p ∈ LogConcaveFamily6.family6) :
    ((law p hp : ProbabilityMeasure ℝ) : Measure ℝ) = rawMeasure p := rfl

theorem integrable_law_moment (p : LogConcaveFamily6.Param)
    (hp : p ∈ LogConcaveFamily6.family6) (k : Fin 3) :
    Integrable (fun x : ℝ ↦ x ^ k.val) (law p hp : Measure ℝ) := by
  change Integrable (fun x : ℝ ↦ x ^ k.val) (rawMeasure p)
  exact integrable_rawMeasure_of_piece (pieceIntegrable_pow k.val hp.1)

theorem integral_law_moment (p : LogConcaveFamily6.Param)
    (hp : p ∈ LogConcaveFamily6.family6) (k : Fin 3) :
    (∫ x : ℝ, x ^ k.val ∂(law p hp : Measure ℝ)) =
      LogConcaveFamily6.isotropicTarget k := by
  change (∫ x : ℝ, x ^ k.val ∂rawMeasure p) = _
  exact (integral_rawMeasure_eq_tagged hp.1 _
    (pieceIntegrable_pow k.val hp.1)).trans (tagged_moment_eq_target hp k)

theorem integral_law_gAlpha (alpha : ℝ) (halpha : 0 ≤ alpha)
    (p : LogConcaveFamily6.Param) (hp : p ∈ LogConcaveFamily6.family6) :
    (∫ x : ℝ, gAlpha alpha x ∂(law p hp : Measure ℝ)) =
      LogConcaveFamily6.objective alpha p := by
  change (∫ x : ℝ, gAlpha alpha x ∂rawMeasure p) = _
  exact integral_rawMeasure_eq_tagged hp.1 _
    (pieceIntegrable_gAlpha halpha hp.1)

theorem law_hasUnitSecondMoment (p : LogConcaveFamily6.Param)
    (hp : p ∈ LogConcaveFamily6.family6) :
    Integrable (fun x : ℝ ↦ x ^ 2) (law p hp : Measure ℝ) ∧
      (∫ x : ℝ, x ^ 2 ∂(law p hp : Measure ℝ)) = 1 := by
  constructor
  · simpa using integrable_law_moment p hp (2 : Fin 3)
  · simpa [LogConcaveFamily6.isotropicTarget] using
      integral_law_moment p hp (2 : Fin 3)

/-! ## A concrete member and the embedded family -/

private def sqrtThree : ℝ := Real.sqrt 3

private def uniformCompactParam : CompactParam :=
  ![-sqrtThree, sqrtThree, -Real.log (2 * sqrtThree), 0, 0, 0]

/-- The centered variance-one uniform density, included only to discharge
nonemptiness of the embedded family. -/
def uniformParam : LogConcaveFamily6.Param := .compact uniformCompactParam

private lemma sqrtThree_pos : 0 < sqrtThree := by
  dsimp [sqrtThree]
  positivity

private lemma sqrtThree_sq : sqrtThree ^ 2 = 3 := by
  dsimp [sqrtThree]
  norm_num

private lemma exp_uniformConstant :
    exp (-Real.log (2 * sqrtThree)) = 1 / (2 * sqrtThree) := by
  rw [Real.exp_neg, Real.exp_log (mul_pos (by norm_num) sqrtThree_pos)]
  ring

theorem uniformParam_mem_family6 :
    uniformParam ∈ LogConcaveFamily6.family6 := by
  constructor
  · change -sqrtThree < 0 ∧ 0 < sqrtThree ∧ (0 : ℝ) ≤ 0
    exact ⟨neg_neg_of_pos sqrtThree_pos, sqrtThree_pos, le_rfl⟩
  · funext k
    fin_cases k
    · change
        (∫ x in -sqrtThree..0,
            x ^ 0 * exp (-Real.log (2 * sqrtThree) + 0 * x)) +
          (∫ x in 0..sqrtThree,
            x ^ 0 * exp
              (-Real.log (2 * sqrtThree) + 0 * x - 0 * (x - 0))) = 1
      simp only [pow_zero, zero_mul, add_zero, sub_zero, one_mul,
        intervalIntegral.integral_const, smul_eq_mul, exp_uniformConstant]
      field_simp [ne_of_gt sqrtThree_pos]
      ring
    · change
        (∫ x in -sqrtThree..0,
            x ^ 1 * exp (-Real.log (2 * sqrtThree) + 0 * x)) +
          (∫ x in 0..sqrtThree,
            x ^ 1 * exp
              (-Real.log (2 * sqrtThree) + 0 * x - 0 * (x - 0))) = 0
      simp only [zero_mul, add_zero, sub_zero, exp_uniformConstant]
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        integral_pow, integral_pow]
      ring
    · change
        (∫ x in -sqrtThree..0,
            x ^ 2 * exp (-Real.log (2 * sqrtThree) + 0 * x)) +
          (∫ x in 0..sqrtThree,
            x ^ 2 * exp
              (-Real.log (2 * sqrtThree) + 0 * x - 0 * (x - 0))) = 1
      simp only [zero_mul, add_zero, sub_zero, exp_uniformConstant]
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        integral_pow, integral_pow]
      have hcube : sqrtThree ^ 3 = 3 * sqrtThree := by
        calc sqrtThree ^ 3 = sqrtThree ^ 2 * sqrtThree := by ring
          _ = 3 * sqrtThree := by rw [sqrtThree_sq]
      have hnegcube : (-sqrtThree) ^ 3 = -(3 * sqrtThree) := by
        rw [neg_pow, hcube]
        norm_num
      norm_num only [Nat.cast_ofNat, Nat.reduceAdd, zero_pow] at *
      rw [hcube, hnegcube]
      field_simp [ne_of_gt sqrtThree_pos]
      ring

/-- Probability laws arising from exact isotropic tagged family-(6)
parameters. -/
def family6Laws : Set (ProbabilityMeasure ℝ) :=
  {mu | ∃ (p : LogConcaveFamily6.Param)
      (hp : p ∈ LogConcaveFamily6.family6), mu = law p hp}

theorem family6Laws_nonempty : family6Laws.Nonempty := by
  exact ⟨law uniformParam uniformParam_mem_family6,
    ⟨uniformParam, uniformParam_mem_family6, rfl⟩⟩

end LogConcaveFamily6.Law

end FlattenedExistenceSection3


/-!
Flattened source section: Family6ProfileCompactification.lean
-/

section FlattenedExistenceSection4

/-!
# A finite-dimensional compact profile space for family (6)

For a density `f` with cdf `F`, the quantile-density profile is

`I(t) = f(F⁻¹(t))`, `0 ≤ t ≤ 1`.

For a two-piece log-affine density, `I` is a nonnegative concave function
which is affine on each side of at most one point `p`.  Up to a positive
scalar it is therefore described by four numbers

`(p, l, h, r) = (p, I(0), I(p), I(1)) / max I`.

This file formalizes the elementary finite-dimensional compactness part of
that idea.  The analytic theorem identifying tagged family-(6) laws with
these profiles (including zero endpoint values and `p = 0,1`) is *not*
postulated.  Instead, the final transfer theorem lists the encoding,
reconstruction, and objective-continuity statements explicitly as
hypotheses.
-/


open Set
open scoped Topology

namespace LogConcaveFamily6.ProfileCompactification

/-- Coordinates are `(p,l,h,r)`: kink mass, left endpoint value, value at
the kink, and right endpoint value. -/
abbrev ProfileParam := Fin 4 → ℝ

def kinkMass (u : ProfileParam) : ℝ := u 0
def leftValue (u : ProfileParam) : ℝ := u 1
def kinkValue (u : ProfileParam) : ℝ := u 2
def rightValue (u : ProfileParam) : ℝ := u 3

/-- The normalized coordinate box. -/
def profileBox : Set ProfileParam :=
  Set.pi Set.univ (fun _ : Fin 4 ↦ Icc (0 : ℝ) 1)

/-- The closed normalized profile parameter set.  The inequality is exactly
the concavity condition

`h ≥ (1-p) l + p r`.

The maximum equation fixes the otherwise irrelevant positive scalar. -/
def normalizedProfiles : Set ProfileParam :=
  profileBox ∩
    ({u | (1 - kinkMass u) * leftValue u +
        kinkMass u * rightValue u ≤ kinkValue u} ∩
      {u | max (leftValue u) (max (kinkValue u) (rightValue u)) = 1})

lemma continuous_kinkMass : Continuous kinkMass := by
  exact continuous_apply 0

lemma continuous_leftValue : Continuous leftValue := by
  exact continuous_apply 1

lemma continuous_kinkValue : Continuous kinkValue := by
  exact continuous_apply 2

lemma continuous_rightValue : Continuous rightValue := by
  exact continuous_apply 3

theorem isCompact_profileBox : IsCompact profileBox := by
  exact isCompact_univ_pi (fun _ ↦ isCompact_Icc)

theorem isClosed_concavityCondition :
    IsClosed {u : ProfileParam |
      (1 - kinkMass u) * leftValue u + kinkMass u * rightValue u ≤
        kinkValue u} := by
  exact isClosed_le
    (((continuous_const.sub continuous_kinkMass).mul continuous_leftValue).add
      (continuous_kinkMass.mul continuous_rightValue))
    continuous_kinkValue

theorem isClosed_normalizationCondition :
    IsClosed {u : ProfileParam |
      max (leftValue u) (max (kinkValue u) (rightValue u)) = 1} := by
  exact isClosed_eq
    (continuous_leftValue.max (continuous_kinkValue.max continuous_rightValue))
    continuous_const

/-- The four normalized profile parameters live in a compact set, including
all endpoint degenerations. -/
theorem isCompact_normalizedProfiles : IsCompact normalizedProfiles := by
  apply IsCompact.inter_right isCompact_profileBox
  exact isClosed_concavityCondition.inter isClosed_normalizationCondition

def constantProfile : ProfileParam := ![(1 / 2 : ℝ), 1, 1, 1]

lemma constantProfile_mem : constantProfile ∈ normalizedProfiles := by
  constructor
  · intro i hi
    fin_cases i <;> norm_num [constantProfile]
  · constructor
    · change (1 - (1 / 2 : ℝ)) * 1 + (1 / 2 : ℝ) * 1 ≤ 1
      norm_num
    · change max (1 : ℝ) (max 1 1) = 1
      norm_num

theorem normalizedProfiles_nonempty : normalizedProfiles.Nonempty :=
  ⟨constantProfile, constantProfile_mem⟩

/-- Any real functional continuous on the normalized profile space attains
its maximum there. -/
theorem exists_profile_maximizer
    (Phi : ProfileParam → ℝ) (hPhi : ContinuousOn Phi normalizedProfiles) :
    ∃ u ∈ normalizedProfiles, IsMaxOn Phi normalizedProfiles u := by
  exact isCompact_normalizedProfiles.exists_isMaxOn
    normalizedProfiles_nonempty hPhi

/-- An explicit, assumption-transparent transfer from compact profiles to
the exact tagged family (6).  This theorem contains no analytic assertion:
the three substantive profile facts are the hypotheses `hencode`, `hdecode`,
and the two objective identities.  Once those facts and continuity of the
profile objective are proved, attainment in the tagged family follows
formally from compactness. -/
theorem family6_attains_of_profile_representation
    (alpha : ℝ)
    (Phi : ProfileParam → ℝ)
    (encode : LogConcaveFamily6.Param → ProfileParam)
    (decode : ProfileParam → LogConcaveFamily6.Param)
    (hPhi : ContinuousOn Phi normalizedProfiles)
    (hencode : ∀ q ∈ LogConcaveFamily6.family6,
      encode q ∈ normalizedProfiles)
    (hdecode : ∀ u ∈ normalizedProfiles,
      decode u ∈ LogConcaveFamily6.family6)
    (hobjective_encode : ∀ q ∈ LogConcaveFamily6.family6,
      Phi (encode q) = LogConcaveFamily6.objective alpha q)
    (hobjective_decode : ∀ u ∈ normalizedProfiles,
      LogConcaveFamily6.objective alpha (decode u) = Phi u) :
    ∃ q ∈ LogConcaveFamily6.family6,
      IsMaxOn (LogConcaveFamily6.objective alpha)
        LogConcaveFamily6.family6 q := by
  obtain ⟨u, hu, humax⟩ := exists_profile_maximizer Phi hPhi
  refine ⟨decode u, hdecode u hu, ?_⟩
  intro q hq
  change LogConcaveFamily6.objective alpha q ≤
    LogConcaveFamily6.objective alpha (decode u)
  rw [hobjective_decode u hu, ← hobjective_encode q hq]
  exact humax (hencode q hq)

/-- An existential version of `family6_attains_of_profile_representation`.
It is often more convenient in a compactification proof: one need not make
arbitrary choices of encoders and decoders away from the two relevant sets.
Every member of `family6` only has to be represented by some normalized
profile, and every normalized profile only has to be realized by some member
of `family6`. -/
theorem family6_attains_of_profile_correspondence
    (alpha : ℝ)
    (Phi : ProfileParam → ℝ)
    (hPhi : ContinuousOn Phi normalizedProfiles)
    (hencode : ∀ q ∈ LogConcaveFamily6.family6, ∃ u ∈ normalizedProfiles,
      Phi u = LogConcaveFamily6.objective alpha q)
    (hdecode : ∀ u ∈ normalizedProfiles,
      ∃ q ∈ LogConcaveFamily6.family6,
        LogConcaveFamily6.objective alpha q = Phi u) :
    ∃ q ∈ LogConcaveFamily6.family6,
      IsMaxOn (LogConcaveFamily6.objective alpha)
        LogConcaveFamily6.family6 q := by
  obtain ⟨u, hu, humax⟩ := exists_profile_maximizer Phi hPhi
  obtain ⟨q, hq, hqu⟩ := hdecode u hu
  refine ⟨q, hq, ?_⟩
  intro r hr
  obtain ⟨v, hv, hvr⟩ := hencode r hr
  change LogConcaveFamily6.objective alpha r ≤
    LogConcaveFamily6.objective alpha q
  rw [hqu, ← hvr]
  exact humax hv

end LogConcaveFamily6.ProfileCompactification

end FlattenedExistenceSection4


/-!
Flattened source section: ProfileObjective.lean
-/

section FlattenedExistenceSection5

/-!
# The analytic objective on normalized one-kink profiles

This file develops the elementary analytic estimates behind the compact
quantile-density-profile model.  If `u = (p,l,h,r)`, then `profileValue u t`
is the piecewise-affine concave profile joining `(0,l)`, `(p,h)`, and
`(1,r)`.  The definitions at `p = 0,1` are chosen so that they are harmless
at the single collapsed endpoint.
-/



open Real Set MeasureTheory
open scoped Interval Topology

namespace LogConcaveFamily6.ProfileCompactification

/-- The piecewise-affine profile determined by `(p,l,h,r)`. -/
def profileValue (u : ProfileParam) (t : ℝ) : ℝ :=
  if ht : t ≤ kinkMass u then
    if hp : kinkMass u = 0 then leftValue u
    else ((kinkMass u - t) * leftValue u + t * kinkValue u) / kinkMass u
  else
    if hp : kinkMass u = 1 then rightValue u
    else ((1 - t) * kinkValue u + (t - kinkMass u) * rightValue u) /
      (1 - kinkMass u)

lemma profile_coordinate_bounds {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) (i : Fin 4) : 0 ≤ u i ∧ u i ≤ 1 := by
  exact hu.1 i (mem_univ i)

lemma kinkMass_nonneg {u : ProfileParam} (hu : u ∈ normalizedProfiles) :
    0 ≤ kinkMass u := (profile_coordinate_bounds hu 0).1

lemma kinkMass_le_one {u : ProfileParam} (hu : u ∈ normalizedProfiles) :
    kinkMass u ≤ 1 := (profile_coordinate_bounds hu 0).2

lemma leftValue_nonneg {u : ProfileParam} (hu : u ∈ normalizedProfiles) :
    0 ≤ leftValue u := (profile_coordinate_bounds hu 1).1

lemma leftValue_le_one {u : ProfileParam} (hu : u ∈ normalizedProfiles) :
    leftValue u ≤ 1 := (profile_coordinate_bounds hu 1).2

lemma kinkValue_nonneg {u : ProfileParam} (hu : u ∈ normalizedProfiles) :
    0 ≤ kinkValue u := (profile_coordinate_bounds hu 2).1

lemma kinkValue_le_one {u : ProfileParam} (hu : u ∈ normalizedProfiles) :
    kinkValue u ≤ 1 := (profile_coordinate_bounds hu 2).2

lemma rightValue_nonneg {u : ProfileParam} (hu : u ∈ normalizedProfiles) :
    0 ≤ rightValue u := (profile_coordinate_bounds hu 3).1

lemma rightValue_le_one {u : ProfileParam} (hu : u ∈ normalizedProfiles) :
    rightValue u ≤ 1 := (profile_coordinate_bounds hu 3).2

lemma profile_concavity {u : ProfileParam} (hu : u ∈ normalizedProfiles) :
    (1 - kinkMass u) * leftValue u + kinkMass u * rightValue u ≤
      kinkValue u := hu.2.1

lemma one_profile_coordinate_eq_one {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) :
    leftValue u = 1 ∨ kinkValue u = 1 ∨ rightValue u = 1 := by
  have hmax := hu.2.2
  change max (leftValue u) (max (kinkValue u) (rightValue u)) = 1 at hmax
  rcases max_choice (leftValue u) (max (kinkValue u) (rightValue u)) with h | h
  · left
    rw [h] at hmax
    exact hmax
  · rw [h] at hmax
    rcases max_choice (kinkValue u) (rightValue u) with h' | h'
    · right; left
      rw [h'] at hmax
      exact hmax
    · right; right
      rw [h'] at hmax
      exact hmax

lemma profileValue_ge_one_sub_of_left_eq_one {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) (hl : leftValue u = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 - t ≤ profileValue u t := by
  have hp0 := kinkMass_nonneg hu
  have hp1 := kinkMass_le_one hu
  have hh0 := kinkValue_nonneg hu
  have hr0 := rightValue_nonneg hu
  have hc := profile_concavity hu
  have hh : 1 - kinkMass u ≤ kinkValue u := by
    rw [hl] at hc
    nlinarith
  by_cases htp : t ≤ kinkMass u
  · by_cases hp : kinkMass u = 0
    · have ht0 : t = 0 := by rw [hp] at htp; linarith [ht.1]
      subst t
      simp [profileValue, hp, hl]
    · have hp' : 0 < kinkMass u := lt_of_le_of_ne hp0 (Ne.symm hp)
      rw [profileValue, dif_pos htp, dif_neg hp, hl]
      apply (le_div_iff₀ hp').2
      nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hh)]
  · have hpt : kinkMass u < t := lt_of_not_ge htp
    by_cases hp : kinkMass u = 1
    · rw [hp] at hpt
      exact (not_lt_of_ge ht.2 hpt).elim
    · have hp' : 0 < 1 - kinkMass u := sub_pos.mpr (lt_of_le_of_ne hp1 hp)
      rw [profileValue, dif_neg htp, dif_neg hp]
      apply (le_div_iff₀ hp').2
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hh),
        mul_nonneg (sub_nonneg.mpr (le_of_lt hpt)) hr0]

lemma profileValue_ge_of_right_eq_one {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) (hr : rightValue u = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t ≤ profileValue u t := by
  have hp0 := kinkMass_nonneg hu
  have hp1 := kinkMass_le_one hu
  have hl0 := leftValue_nonneg hu
  have hh0 := kinkValue_nonneg hu
  have hc := profile_concavity hu
  have hh : kinkMass u ≤ kinkValue u := by
    rw [hr] at hc
    nlinarith
  by_cases htp : t ≤ kinkMass u
  · by_cases hp : kinkMass u = 0
    · have ht0 : t = 0 := by rw [hp] at htp; linarith [ht.1]
      subst t
      simp [profileValue, hp, leftValue_nonneg hu]
    · have hp' : 0 < kinkMass u := lt_of_le_of_ne hp0 (Ne.symm hp)
      rw [profileValue, dif_pos htp, dif_neg hp]
      apply (le_div_iff₀ hp').2
      nlinarith [mul_nonneg (sub_nonneg.mpr htp) hl0,
        mul_nonneg ht.1 (sub_nonneg.mpr hh)]
  · have hpt : kinkMass u < t := lt_of_not_ge htp
    by_cases hp : kinkMass u = 1
    · rw [hp] at hpt
      exact (not_lt_of_ge ht.2 hpt).elim
    · have hp' : 0 < 1 - kinkMass u := sub_pos.mpr (lt_of_le_of_ne hp1 hp)
      rw [profileValue, dif_neg htp, dif_neg hp, hr]
      apply (le_div_iff₀ hp').2
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hh)]

lemma profileValue_ge_left_of_kink_eq_one {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) (hh : kinkValue u = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htp : t ≤ kinkMass u) : t ≤ profileValue u t := by
  have hp0 := kinkMass_nonneg hu
  have hp1 := kinkMass_le_one hu
  by_cases hp : kinkMass u = 0
  · rw [profileValue, dif_pos htp, dif_pos hp]
    nlinarith [leftValue_nonneg hu]
  · have hp' : 0 < kinkMass u := lt_of_le_of_ne hp0 (Ne.symm hp)
    rw [profileValue, dif_pos htp, dif_neg hp, hh]
    apply (le_div_iff₀ hp').2
    have htp_mul : t * kinkMass u ≤ t := by
      simpa using mul_le_mul_of_nonneg_left hp1 ht.1
    nlinarith [mul_nonneg (sub_nonneg.mpr htp) (leftValue_nonneg hu)]

lemma profileValue_ge_right_of_kink_eq_one {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) (hh : kinkValue u = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (htp : ¬ t ≤ kinkMass u) : 1 - t ≤ profileValue u t := by
  have hp0 := kinkMass_nonneg hu
  have hp1 := kinkMass_le_one hu
  have hpt : kinkMass u < t := lt_of_not_ge htp
  by_cases hp : kinkMass u = 1
  · rw [hp] at hpt
    exact (not_lt_of_ge ht.2 hpt).elim
  · have hp' : 0 < 1 - kinkMass u := sub_pos.mpr (lt_of_le_of_ne hp1 hp)
    rw [profileValue, dif_neg htp, dif_neg hp, hh]
    apply (le_div_iff₀ hp').2
    have hmul : (1 - t) * (1 - kinkMass u) ≤ 1 - t := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hp0]
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_lt hpt))
      (rightValue_nonneg hu)]

/-- Every normalized concave one-kink profile dominates the universal tent
`min t (1-t)`.  In particular it is strictly positive in the open unit
interval, uniformly in the profile parameters. -/
theorem min_le_profileValue {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    min t (1 - t) ≤ profileValue u t := by
  rcases one_profile_coordinate_eq_one hu with hl | hh | hr
  · exact (min_le_right _ _).trans
      (profileValue_ge_one_sub_of_left_eq_one hu hl ht)
  · by_cases htp : t ≤ kinkMass u
    · exact (min_le_left _ _).trans
        (profileValue_ge_left_of_kink_eq_one hu hh ht htp)
    · exact (min_le_right _ _).trans
        (profileValue_ge_right_of_kink_eq_one hu hh ht htp)
  · exact (min_le_left _ _).trans
      (profileValue_ge_of_right_eq_one hu hr ht)

theorem profileValue_pos {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < profileValue u t := by
  have hmin : 0 < min t (1 - t) := lt_min ht.1 (sub_pos.mpr ht.2)
  exact hmin.trans_le (min_le_profileValue hu ⟨ht.1.le, ht.2.le⟩)

/-- For every admissible profile, the profile value is continuous away from
the two possibly collapsed endpoints. -/
theorem continuousOn_profileValue_Ioo (u : ProfileParam) :
    ContinuousOn (profileValue u) (Ioo (0 : ℝ) 1) := by
  by_cases hp0 : kinkMass u = 0
  · have hformula : ∀ t ∈ Ioo (0 : ℝ) 1,
        profileValue u t =
          (1 - t) * kinkValue u + t * rightValue u := by
      intro t ht
      simp [profileValue, hp0, not_le_of_gt ht.1]
    have hc : Continuous (fun t : ℝ ↦
        (1 - t) * kinkValue u + t * rightValue u) := by fun_prop
    exact hc.continuousOn.congr (fun t ht ↦ hformula t ht)
  · by_cases hp1 : kinkMass u = 1
    · have hformula : ∀ t ∈ Ioo (0 : ℝ) 1,
          profileValue u t =
            (1 - t) * leftValue u + t * kinkValue u := by
        intro t ht
        have htp : t ≤ kinkMass u := by rw [hp1]; exact ht.2.le
        rw [profileValue, dif_pos htp, dif_neg hp0, hp1]
        ring
      have hc : Continuous (fun t : ℝ ↦
          (1 - t) * leftValue u + t * kinkValue u) := by fun_prop
      exact hc.continuousOn.congr (fun t ht ↦ hformula t ht)
    · let left : ℝ → ℝ := fun t ↦
          ((kinkMass u - t) * leftValue u + t * kinkValue u) / kinkMass u
      let right : ℝ → ℝ := fun t ↦
          ((1 - t) * kinkValue u + (t - kinkMass u) * rightValue u) /
            (1 - kinkMass u)
      have hleft : Continuous left := by fun_prop
      have hright : Continuous right := by fun_prop
      have hmatch : ∀ t : ℝ, t = kinkMass u → left t = right t := by
        intro t ht
        subst t
        have hden : 1 - kinkMass u ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
        simp [left, right, hp0, hden]
      have hpiece : Continuous (fun t : ℝ ↦
          if t ≤ kinkMass u then left t else right t) :=
        hleft.if_le hright continuous_id continuous_const hmatch
      apply hpiece.continuousOn.congr
      intro t ht
      by_cases htp : t ≤ kinkMass u
      · simp [profileValue, left, htp, hp0]
      · simp [profileValue, right, htp, hp1]

/-- The reciprocal profile is interval-integrable between any two interior
quantile levels. -/
theorem intervalIntegrable_inv_profileValue {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun t ↦ (profileValue u t)⁻¹) volume a b := by
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    rw [mem_uIcc] at ht
    rcases ht with ht | ht
    · exact ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
    · exact ⟨hb.1.trans_le ht.1, ht.2.trans_lt ha.2⟩
  have hc : ContinuousOn (fun t ↦ (profileValue u t)⁻¹) (uIcc a b) :=
    ((continuousOn_profileValue_Ioo u).mono hsub).inv₀
      (fun t ht ↦ (profileValue_pos hu (hsub ht)).ne')
  exact hc.intervalIntegrable

/-! ## Continuity with respect to the profile parameter -/

/-- A denominator-regularized formula for evaluating a profile at a fixed
interior quantile.  On the branch where it is used, each `max` equals the
original denominator.  Unlike the raw formula, this auxiliary expression is
continuous on the whole parameter space. -/
def regularProfileValue (t : ℝ) (u : ProfileParam) : ℝ :=
  if t ≤ kinkMass u then
    ((kinkMass u - t) * leftValue u + t * kinkValue u) /
      max (kinkMass u) (t / 2)
  else
    ((1 - t) * kinkValue u + (t - kinkMass u) * rightValue u) /
      max (1 - kinkMass u) ((1 - t) / 2)

theorem continuous_regularProfileValue {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Continuous (regularProfileValue t) := by
  let left : ProfileParam → ℝ := fun u ↦
      ((kinkMass u - t) * leftValue u + t * kinkValue u) /
        max (kinkMass u) (t / 2)
  let right : ProfileParam → ℝ := fun u ↦
      ((1 - t) * kinkValue u + (t - kinkMass u) * rightValue u) /
        max (1 - kinkMass u) ((1 - t) / 2)
  have hleft : Continuous left := by
    apply Continuous.div
    · exact ((continuous_kinkMass.sub continuous_const).mul continuous_leftValue).add
        (continuous_const.mul continuous_kinkValue)
    · exact continuous_kinkMass.max continuous_const
    · intro u
      have : 0 < max (kinkMass u) (t / 2) :=
        (half_pos ht.1).trans_le (le_max_right _ _)
      exact this.ne'
  have hright : Continuous right := by
    apply Continuous.div
    · exact (continuous_const.mul continuous_kinkValue).add
        ((continuous_const.sub continuous_kinkMass).mul continuous_rightValue)
    · exact (continuous_const.sub continuous_kinkMass).max continuous_const
    · intro u
      have : 0 < max (1 - kinkMass u) ((1 - t) / 2) :=
        (half_pos (sub_pos.mpr ht.2)).trans_le (le_max_right _ _)
      exact this.ne'
  have hmatch : ∀ u : ProfileParam, t = kinkMass u → left u = right u := by
    intro u hu
    have ht0 : t ≠ 0 := ne_of_gt ht.1
    have ht1 : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht.2)
    have hmaxl : max t (t / 2) = t := max_eq_left (half_le_self ht.1.le)
    have hmaxr : max (1 - t) ((1 - t) / 2) = 1 - t :=
      max_eq_left (half_le_self (sub_nonneg.mpr ht.2.le))
    dsimp [left, right]
    rw [← hu]
    simp [hmaxl, hmaxr, ht0, ht1]
  change Continuous (fun u : ProfileParam ↦
    if t ≤ kinkMass u then left u else right u)
  exact hleft.if_le hright continuous_const continuous_kinkMass hmatch

theorem regularProfileValue_eq_profileValue {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (u : ProfileParam) : regularProfileValue t u = profileValue u t := by
  by_cases htp : t ≤ kinkMass u
  · have hp0 : kinkMass u ≠ 0 := by
      exact ne_of_gt (ht.1.trans_le htp)
    have hhalf : t / 2 ≤ kinkMass u := (half_le_self ht.1.le).trans htp
    simp [regularProfileValue, profileValue, htp, hp0, max_eq_left hhalf]
  · have hpt : kinkMass u < t := lt_of_not_ge htp
    have hp1 : kinkMass u ≠ 1 := by
      intro hp
      rw [hp] at hpt
      exact (not_lt_of_ge ht.2.le hpt)
    have hhalf : (1 - t) / 2 ≤ 1 - kinkMass u :=
      (half_le_self (sub_nonneg.mpr ht.2.le)).trans (by linarith)
    simp [regularProfileValue, profileValue, htp, hp1, max_eq_left hhalf]

/-- Evaluation at any fixed interior quantile is continuous in all four
profile coordinates. -/
theorem continuous_profileValue_at {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    Continuous (fun u : ProfileParam ↦ profileValue u t) := by
  exact (continuous_regularProfileValue ht).congr
    (fun u ↦ regularProfileValue_eq_profileValue ht u)

/-- Along the interval between `1/2` and `t`, the tent function is bounded
below by its value at `t`. -/
lemma tent_lower_on_uIcc_half {t s : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hs : s ∈ uIcc (1 / 2 : ℝ) t) :
    min t (1 - t) ≤ min s (1 - s) := by
  rcases le_total t (1 / 2 : ℝ) with htH | hHt
  · have hs' : s ∈ Icc t (1 / 2 : ℝ) := by
      rcases mem_uIcc.mp hs with hs | hs
      · exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
      · exact hs
    have htmin : t ≤ 1 - t := by linarith [htH]
    have hsmin : s ≤ 1 - s := by linarith [hs'.2]
    rw [min_eq_left htmin, min_eq_left hsmin]
    exact hs'.1
  · have hs' : s ∈ Icc (1 / 2 : ℝ) t := by
      rcases mem_uIcc.mp hs with hs | hs
      · exact hs
      · exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have htmin : 1 - t ≤ t := by linarith [hHt]
    have hsmin : 1 - s ≤ s := by linarith [hs'.1]
    rw [min_eq_right htmin, min_eq_right hsmin]
    linarith [hs'.2]

/-- An uncentered quantile reconstructed from the reciprocal profile, with
the harmless anchoring convention `R(1/2)=0`. -/
def rawQuantile (u : ProfileParam) (t : ℝ) : ℝ :=
  ∫ s in (1 / 2 : ℝ)..t, (profileValue u s)⁻¹

/-- For every fixed interior quantile, the reconstructed raw quantile is
continuous on the compact normalized profile space. -/
theorem continuousOn_rawQuantile_at {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun u : ProfileParam ↦ rawQuantile u t) normalizedProfiles := by
  intro u hu
  let e : ℝ := min t (1 - t)
  have he : 0 < e := lt_min ht.1 (sub_pos.mpr ht.2)
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (F := fun u s ↦ (profileValue u s)⁻¹)
      (bound := fun _ ↦ e⁻¹)
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact (intervalIntegrable_iff.mp (intervalIntegrable_inv_profileValue hv
      (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by norm_num) ht)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with v hv
    filter_upwards with s
    intro hs
    have hs' : s ∈ uIcc (1 / 2 : ℝ) t := Ioc_subset_Icc_self hs
    have hsI : s ∈ Ioo (0 : ℝ) 1 := by
      rcases mem_uIcc.mp hs' with hs' | hs'
      · exact ⟨(by linarith), hs'.2.trans_lt ht.2⟩
      · exact ⟨ht.1.trans_le hs'.1, by linarith⟩
    have hprofile : e ≤ profileValue v s :=
      (tent_lower_on_uIcc_half ht hs').trans
        (min_le_profileValue hv ⟨hsI.1.le, hsI.2.le⟩)
    have hpos : 0 < profileValue v s := he.trans_le hprofile
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)]
    exact (inv_le_inv₀ hpos he).2 hprofile
  · exact intervalIntegrable_const
  · filter_upwards with s
    intro hs
    have hs' : s ∈ uIcc (1 / 2 : ℝ) t := Ioc_subset_Icc_self hs
    have hsI : s ∈ Ioo (0 : ℝ) 1 := by
      rcases mem_uIcc.mp hs' with hs' | hs'
      · exact ⟨(by linarith), hs'.2.trans_lt ht.2⟩
      · exact ⟨ht.1.trans_le hs'.1, by linarith⟩
    exact (continuous_profileValue_at hsI).continuousAt.continuousWithinAt.inv₀
      (profileValue_pos hu hsI).ne'

lemma rawQuantile_abs_le_neg_log_left {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (htH : t ≤ 1 / 2) :
    |rawQuantile u t| ≤ -log t := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hInt := intervalIntegrable_inv_profileValue hu ht hhalf
  have hnonneg : 0 ≤ ∫ s in t..(1 / 2 : ℝ), (profileValue u s)⁻¹ := by
    apply intervalIntegral.integral_nonneg htH
    intro s hs
    exact inv_nonneg.mpr (le_of_lt (profileValue_pos hu
      ⟨ht.1.trans_le hs.1, hs.2.trans_lt hhalf.2⟩))
  have hraw : rawQuantile u t =
      -(∫ s in t..(1 / 2 : ℝ), (profileValue u s)⁻¹) := by
    rw [rawQuantile, intervalIntegral.integral_symm]
  have hmono : (∫ s in t..(1 / 2 : ℝ), (profileValue u s)⁻¹) ≤
      ∫ s in t..(1 / 2 : ℝ), s⁻¹ := by
    apply intervalIntegral.integral_mono_on htH hInt
    · have hc : ContinuousOn (fun s : ℝ ↦ s⁻¹) (Icc t (1 / 2 : ℝ)) :=
        continuousOn_id.inv₀ (fun s hs ↦ (ne_of_gt (ht.1.trans_le hs.1)))
      have hc' : ContinuousOn (fun s : ℝ ↦ s⁻¹) (uIcc t (1 / 2 : ℝ)) := by
        simpa only [uIcc_of_le htH] using hc
      exact hc'.intervalIntegrable
    · intro s hs
      have hsI : s ∈ Icc (0 : ℝ) 1 :=
        ⟨(ht.1.trans_le hs.1).le, hs.2.trans (by norm_num)⟩
      have hspos : 0 < s := ht.1.trans_le hs.1
      have hsmin : min s (1 - s) = s := min_eq_left (by linarith [hs.2])
      have hsprof : s ≤ profileValue u s := by
        calc
          s = min s (1 - s) := hsmin.symm
          _ ≤ profileValue u s := min_le_profileValue hu hsI
      exact (inv_le_inv₀ (profileValue_pos hu
        ⟨hspos, hs.2.trans_lt hhalf.2⟩) hspos).2 hsprof
  rw [hraw, abs_neg, abs_of_nonneg hnonneg]
  calc
    (∫ s in t..(1 / 2 : ℝ), (profileValue u s)⁻¹) ≤
        ∫ s in t..(1 / 2 : ℝ), s⁻¹ := hmono
    _ = log ((1 / 2 : ℝ) / t) := integral_inv_of_pos ht.1 (by norm_num)
    _ = log (1 / 2 : ℝ) - log t := by
      rw [Real.log_div (by norm_num) ht.1.ne']
    _ ≤ -log t := by
      have := Real.log_nonpos (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      linarith

lemma rawQuantile_abs_le_neg_log_right {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hHt : 1 / 2 ≤ t) :
    |rawQuantile u t| ≤ -log (1 - t) := by
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hInt := intervalIntegrable_inv_profileValue hu hhalf ht
  have hnonneg : 0 ≤ ∫ s in (1 / 2 : ℝ)..t, (profileValue u s)⁻¹ := by
    apply intervalIntegral.integral_nonneg hHt
    intro s hs
    exact inv_nonneg.mpr (le_of_lt (profileValue_pos hu
      ⟨hhalf.1.trans_le hs.1, hs.2.trans_lt ht.2⟩))
  have hmono : (∫ s in (1 / 2 : ℝ)..t, (profileValue u s)⁻¹) ≤
      ∫ s in (1 / 2 : ℝ)..t, (1 - s)⁻¹ := by
    apply intervalIntegral.integral_mono_on hHt hInt
    · have hc : ContinuousOn (fun s : ℝ ↦ (1 - s)⁻¹) (Icc (1 / 2 : ℝ) t) :=
        ((continuous_const.sub continuous_id).continuousOn).inv₀
          (fun s hs ↦ (ne_of_gt (sub_pos.mpr (hs.2.trans_lt ht.2))))
      have hc' : ContinuousOn (fun s : ℝ ↦ (1 - s)⁻¹)
          (uIcc (1 / 2 : ℝ) t) := by
        simpa only [uIcc_of_le hHt] using hc
      exact hc'.intervalIntegrable
    · intro s hs
      have hsI : s ∈ Icc (0 : ℝ) 1 :=
        ⟨(by linarith [hs.1]), hs.2.trans ht.2.le⟩
      have hspos : 0 < 1 - s := sub_pos.mpr (hs.2.trans_lt ht.2)
      have hsmin : min s (1 - s) = 1 - s := min_eq_right (by linarith [hs.1])
      have hsprof : 1 - s ≤ profileValue u s := by
        calc
          1 - s = min s (1 - s) := hsmin.symm
          _ ≤ profileValue u s := min_le_profileValue hu hsI
      exact (inv_le_inv₀ (profileValue_pos hu
        ⟨hhalf.1.trans_le hs.1, hs.2.trans_lt ht.2⟩) hspos).2 hsprof
  rw [rawQuantile, abs_of_nonneg hnonneg]
  calc
    (∫ s in (1 / 2 : ℝ)..t, (profileValue u s)⁻¹) ≤
        ∫ s in (1 / 2 : ℝ)..t, (1 - s)⁻¹ := hmono
    _ = ∫ y in (1 - t)..(1 / 2 : ℝ), y⁻¹ := by
      convert (intervalIntegral.integral_comp_sub_left
        (f := fun y : ℝ ↦ y⁻¹) (a := (1 / 2 : ℝ)) (b := t) 1) using 1 <;>
        norm_num
    _ = log ((1 / 2 : ℝ) / (1 - t)) :=
      integral_inv_of_pos (sub_pos.mpr ht.2) (by norm_num)
    _ = log (1 / 2 : ℝ) - log (1 - t) := by
      rw [Real.log_div (by norm_num) (sub_pos.mpr ht.2).ne']
    _ ≤ -log (1 - t) := by
      have := Real.log_nonpos (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      linarith

lemma neg_log_le_four_mul_rpow {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    -log x ≤ 4 * x ^ (-(1 / 4 : ℝ)) := by
  have hypos : 0 < x ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hx.1 _
  have hlog := Real.log_le_sub_one_of_pos hypos
  rw [Real.log_rpow hx.1] at hlog
  have hynonneg : 0 ≤ x ^ (-(1 / 4 : ℝ)) := hypos.le
  nlinarith

/-- A single integrable power envelope for all reconstructed quantiles. -/
def quantileEnvelope (t : ℝ) : ℝ :=
  4 * (t ^ (-(1 / 4 : ℝ)) + (1 - t) ^ (-(1 / 4 : ℝ)))

theorem abs_rawQuantile_le_envelope {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    |rawQuantile u t| ≤ quantileEnvelope t := by
  have htPow : 0 ≤ t ^ (-(1 / 4 : ℝ)) := (Real.rpow_pos_of_pos ht.1 _).le
  have h1Pow : 0 ≤ (1 - t) ^ (-(1 / 4 : ℝ)) :=
    (Real.rpow_pos_of_pos (sub_pos.mpr ht.2) _).le
  rcases le_total t (1 / 2 : ℝ) with htH | hHt
  · calc
      |rawQuantile u t| ≤ -log t := rawQuantile_abs_le_neg_log_left hu ht htH
      _ ≤ 4 * t ^ (-(1 / 4 : ℝ)) := neg_log_le_four_mul_rpow ht
      _ ≤ quantileEnvelope t := by simp [quantileEnvelope]; nlinarith
  · calc
      |rawQuantile u t| ≤ -log (1 - t) := rawQuantile_abs_le_neg_log_right hu ht hHt
      _ ≤ 4 * (1 - t) ^ (-(1 / 4 : ℝ)) :=
        neg_log_le_four_mul_rpow ⟨sub_pos.mpr ht.2, by linarith [ht.1]⟩
      _ ≤ quantileEnvelope t := by simp [quantileEnvelope]; nlinarith

/-- For a fixed profile, the reconstructed raw quantile is continuous at
every interior probability level. -/
theorem continuousOn_rawQuantile_Ioo {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) :
    ContinuousOn (rawQuantile u) (Ioo (0 : ℝ) 1) := by
  intro t ht
  let a : ℝ := t / 2
  let b : ℝ := (t + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith [ht.1]
  have hat : a < t := by dsimp [a]; linarith [ht.1]
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hb : b < 1 := by dsimp [b]; linarith [ht.2]
  have hleft : min (1 / 2 : ℝ) a ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact lt_min (by norm_num) ha
    · exact (min_le_left _ _).trans_lt (by norm_num)
  have hright : max (1 / 2 : ℝ) b ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_left _ _)
    · exact max_lt (by norm_num) hb
  have hInt : IntervalIntegrable (fun s ↦ (profileValue u s)⁻¹) volume
      (min (1 / 2 : ℝ) a) (max (1 / 2 : ℝ) b) :=
    intervalIntegrable_inv_profileValue hu hleft hright
  have hc := intervalIntegral.continuousWithinAt_primitive
    (f := fun s ↦ (profileValue u s)⁻¹)
    (a := (1 / 2 : ℝ)) (b₀ := t) (b₁ := a) (b₂ := b)
    (by simp) hInt
  change ContinuousWithinAt
    (fun q : ℝ ↦ ∫ s in (1 / 2 : ℝ)..q, (profileValue u s)⁻¹)
    (Ioo (0 : ℝ) 1) t
  exact (hc.continuousAt (Icc_mem_nhds hat htb)).continuousWithinAt

theorem aestronglyMeasurable_rawQuantile {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) :
    AEStronglyMeasurable (rawQuantile u) (volume.restrict (Ioo (0 : ℝ) 1)) :=
  (continuousOn_rawQuantile_Ioo hu).aestronglyMeasurable measurableSet_Ioo

theorem aestronglyMeasurable_rawQuantile_Ioc {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) :
    AEStronglyMeasurable (rawQuantile u)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hind : AEStronglyMeasurable
      ((Ioo (0 : ℝ) 1).indicator (rawQuantile u)) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioo).2
      (aestronglyMeasurable_rawQuantile hu)
  have hind' : AEStronglyMeasurable
      ((Ioo (0 : ℝ) 1).indicator (rawQuantile u))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hind.mono_measure Measure.restrict_le_self
  apply hind'.congr
  have hnull : (volume.restrict (Ioc (0 : ℝ) 1)) ({1} : Set ℝ) = 0 := by
    rw [Measure.restrict_apply (s := Ioc (0 : ℝ) 1)
      (t := ({1} : Set ℝ)) (measurableSet_singleton 1)]
    simp
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    compl_mem_ae_iff.mpr hnull] with t ht hne
  have ht1 : t ≠ 1 := by simpa using hne
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.lt_of_ne ht1⟩
  simp [htI]

theorem intervalIntegrable_quantileEnvelope :
    IntervalIntegrable quantileEnvelope volume 0 1 := by
  have hpow : IntervalIntegrable (fun t : ℝ ↦ t ^ (-(1 / 4 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hreflect : IntervalIntegrable
      (fun t : ℝ ↦ (1 - t) ^ (-(1 / 4 : ℝ))) volume 0 1 := by
    convert (hpow.comp_sub_left 1).symm using 1 <;> norm_num
  change IntervalIntegrable
    (fun t : ℝ ↦ 4 * (t ^ (-(1 / 4 : ℝ)) + (1 - t) ^ (-(1 / 4 : ℝ))))
    volume 0 1
  exact (hpow.add hreflect).const_mul 4

def quantileSquareEnvelope (t : ℝ) : ℝ :=
  32 * (t ^ (-(1 / 2 : ℝ)) + (1 - t) ^ (-(1 / 2 : ℝ)))

lemma sq_rpow_neg_quarter {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (-(1 / 4 : ℝ))) ^ 2 = x ^ (-(1 / 2 : ℝ)) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hx]
  congr 1
  norm_num

theorem sq_rawQuantile_le_squareEnvelope {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (rawQuantile u t) ^ 2 ≤ quantileSquareEnvelope t := by
  let a : ℝ := t ^ (-(1 / 4 : ℝ))
  let b : ℝ := (1 - t) ^ (-(1 / 4 : ℝ))
  have ha : 0 ≤ a := (Real.rpow_pos_of_pos ht.1 _).le
  have hb : 0 ≤ b := (Real.rpow_pos_of_pos (sub_pos.mpr ht.2) _).le
  have hab : |rawQuantile u t| ≤ 4 * (a + b) := by
    simpa only [quantileEnvelope, a, b] using abs_rawQuantile_le_envelope hu ht
  have hsquare : |rawQuantile u t| ^ 2 ≤ (4 * (a + b)) ^ 2 := by
    exact pow_le_pow_left₀ (abs_nonneg _) hab 2
  have hsum : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
  rw [sq_abs] at hsquare
  calc
    rawQuantile u t ^ 2 ≤ (4 * (a + b)) ^ 2 := hsquare
    _ ≤ 32 * (a ^ 2 + b ^ 2) := by nlinarith
    _ = quantileSquareEnvelope t := by
      rw [show a ^ 2 = t ^ (-(1 / 2 : ℝ)) from sq_rpow_neg_quarter ht.1.le,
        show b ^ 2 = (1 - t) ^ (-(1 / 2 : ℝ)) from
          sq_rpow_neg_quarter (sub_nonneg.mpr ht.2.le)]
      rfl

theorem intervalIntegrable_quantileSquareEnvelope :
    IntervalIntegrable quantileSquareEnvelope volume 0 1 := by
  have hpow : IntervalIntegrable (fun t : ℝ ↦ t ^ (-(1 / 2 : ℝ))) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hreflect : IntervalIntegrable
      (fun t : ℝ ↦ (1 - t) ^ (-(1 / 2 : ℝ))) volume 0 1 := by
    convert (hpow.comp_sub_left 1).symm using 1 <;> norm_num
  change IntervalIntegrable
    (fun t : ℝ ↦ 32 * (t ^ (-(1 / 2 : ℝ)) + (1 - t) ^ (-(1 / 2 : ℝ))))
    volume 0 1
  exact (hpow.add hreflect).const_mul 32

/-! ## Centering and variance normalization -/

def profileMean (u : ProfileParam) : ℝ :=
  ∫ t in (0 : ℝ)..1, rawQuantile u t

theorem continuousOn_profileMean :
    ContinuousOn profileMean normalizedProfiles := by
  intro u hu
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (F := fun u t ↦ rawQuantile u t) (bound := quantileEnvelope)
  · filter_upwards [self_mem_nhdsWithin] with v hv
    simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using
      aestronglyMeasurable_rawQuantile_Ioc hv
  · filter_upwards [self_mem_nhdsWithin] with v hv
    have hnull : volume ({1} : Set ℝ) = 0 := by simp
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht1
    intro ht
    have ht1' : t ≠ 1 := by simpa using ht1
    have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨htIoc.1, htIoc.2.lt_of_ne ht1'⟩
    rw [Real.norm_eq_abs]
    exact abs_rawQuantile_le_envelope hv htI
  · exact intervalIntegrable_quantileEnvelope
  · have hnull : volume ({1} : Set ℝ) = 0 := by simp
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht1
    intro ht
    have ht1' : t ≠ 1 := by simpa using ht1
    have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨htIoc.1, htIoc.2.lt_of_ne ht1'⟩
    exact continuousOn_rawQuantile_at htI u hu

def centeredQuantile (u : ProfileParam) (t : ℝ) : ℝ :=
  rawQuantile u t - profileMean u

def profileVariance (u : ProfileParam) : ℝ :=
  ∫ t in (0 : ℝ)..1, (centeredQuantile u t) ^ 2

theorem continuousOn_profileVariance :
    ContinuousOn profileVariance normalizedProfiles := by
  intro u hu
  let C : ℝ := |profileMean u| + 1
  let bound : ℝ → ℝ := fun t ↦ 2 * (quantileSquareEnvelope t + C ^ 2)
  have hmeanEvent : ∀ᶠ v in nhdsWithin u normalizedProfiles,
      dist (profileMean v) (profileMean u) < 1 :=
    (continuousOn_profileMean u hu) (Metric.ball_mem_nhds _ zero_lt_one)
  have hboundInt : IntervalIntegrable bound volume 0 1 := by
    have hc : IntervalIntegrable (fun _ : ℝ ↦ C ^ 2) volume 0 1 := intervalIntegrable_const
    exact (intervalIntegrable_quantileSquareEnvelope.add hc).const_mul 2
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (F := fun v t ↦ (centeredQuantile v t) ^ 2) (bound := bound)
  · filter_upwards [self_mem_nhdsWithin] with v hv
    have hm := aestronglyMeasurable_rawQuantile_Ioc hv
    have hcenter : AEStronglyMeasurable (centeredQuantile v)
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
      exact hm.sub aestronglyMeasurable_const
    have hmul : AEStronglyMeasurable
        (fun t ↦ centeredQuantile v t * centeredQuantile v t)
        (volume.restrict (Ioc (0 : ℝ) 1)) := by
      exact (hcenter.mul hcenter).congr (Filter.Eventually.of_forall (fun _ ↦ rfl))
    simpa [pow_two, uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hmul
  · filter_upwards [self_mem_nhdsWithin, hmeanEvent] with v hv hmean
    have hnull : volume ({1} : Set ℝ) = 0 := by simp
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht1
    intro ht
    have ht1' : t ≠ 1 := by simpa using ht1
    have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨htIoc.1, htIoc.2.lt_of_ne ht1'⟩
    have hraw := sq_rawQuantile_le_squareEnvelope hv htI
    have hmeanAbs : |profileMean v| ≤ C := by
      rw [Real.dist_eq] at hmean
      dsimp [C]
      calc
        |profileMean v| = |profileMean u + (profileMean v - profileMean u)| := by
          congr 1
          ring
        _ ≤ |profileMean u| + |profileMean v - profileMean u| :=
          abs_add_le _ _
        _ ≤ |profileMean u| + 1 := by linarith
    have hcenterSq : (centeredQuantile v t) ^ 2 ≤
        2 * ((rawQuantile v t) ^ 2 + (profileMean v) ^ 2) := by
      dsimp [centeredQuantile]
      nlinarith [sq_nonneg (rawQuantile v t + profileMean v)]
    have hmeanSq : (profileMean v) ^ 2 ≤ C ^ 2 := by
      have hC : 0 ≤ C := by dsimp only [C]; positivity
      calc
        (profileMean v) ^ 2 = |profileMean v| ^ 2 := (sq_abs _).symm
        _ ≤ C ^ 2 := (sq_le_sq₀ (abs_nonneg _) hC).2 hmeanAbs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    dsimp [bound]
    nlinarith
  · exact hboundInt
  · have hnull : volume ({1} : Set ℝ) = 0 := by simp
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht1
    intro ht
    have ht1' : t ≠ 1 := by simpa using ht1
    have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨htIoc.1, htIoc.2.lt_of_ne ht1'⟩
    have hc : ContinuousWithinAt (fun v : ProfileParam ↦ centeredQuantile v t)
        normalizedProfiles u := by
      exact (continuousOn_rawQuantile_at htI u hu).sub (continuousOn_profileMean u hu)
    exact hc.pow 2

theorem intervalIntegrable_centeredQuantile_sq {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) :
    IntervalIntegrable (fun t ↦ (centeredQuantile u t) ^ 2) volume 0 1 := by
  let C : ℝ := |profileMean u|
  let bound : ℝ → ℝ := fun t ↦ 2 * (quantileSquareEnvelope t + C ^ 2)
  have hboundInt : IntervalIntegrable bound volume 0 1 := by
    have hc : IntervalIntegrable (fun _ : ℝ ↦ C ^ 2) volume 0 1 := intervalIntegrable_const
    exact (intervalIntegrable_quantileSquareEnvelope.add hc).const_mul 2
  have hm := aestronglyMeasurable_rawQuantile_Ioc hu
  have hcenter : AEStronglyMeasurable (centeredQuantile u)
      (volume.restrict (Ioc (0 : ℝ) 1)) := hm.sub aestronglyMeasurable_const
  have hsq : AEStronglyMeasurable (fun t ↦ (centeredQuantile u t) ^ 2)
      (volume.restrict (uIoc (0 : ℝ) 1)) := by
    have hmul : AEStronglyMeasurable
        (fun t ↦ centeredQuantile u t * centeredQuantile u t)
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      (hcenter.mul hcenter).congr (Filter.Eventually.of_forall (fun _ ↦ rfl))
    simpa [pow_two, uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hmul
  apply hboundInt.mono_fun' hsq
  have hnull : volume ({1} : Set ℝ) = 0 := by simp
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_mono Measure.restrict_le_self (compl_mem_ae_iff.mpr hnull)] with t ht ht1
  have ht1' : t ≠ 1 := by simpa using ht1
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
    simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨htIoc.1, htIoc.2.lt_of_ne ht1'⟩
  have hraw := sq_rawQuantile_le_squareEnvelope hu htI
  have hcenterSq : (centeredQuantile u t) ^ 2 ≤
      2 * ((rawQuantile u t) ^ 2 + (profileMean u) ^ 2) := by
    dsimp [centeredQuantile]
    nlinarith [sq_nonneg (rawQuantile u t + profileMean u)]
  have hmeanSq : (profileMean u) ^ 2 = C ^ 2 := by
    dsimp [C]
    exact (sq_abs _).symm
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  dsimp [bound]
  rw [← hmeanSq]
  nlinarith

/-- Reconstructed quantiles are strictly increasing on `(0,1)`. -/
theorem strictMonoOn_rawQuantile {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) :
    StrictMonoOn (rawQuantile u) (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hIa := intervalIntegrable_inv_profileValue hu hhalf ha
  have hIab := intervalIntegrable_inv_profileValue hu ha hb
  have hpos : 0 < ∫ t in a..b, (profileValue u t)⁻¹ := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hIab
    · intro t ht
      exact inv_pos.mpr (profileValue_pos hu ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩)
    · exact hab
  have hadd := intervalIntegral.integral_add_adjacent_intervals hIa hIab
  change rawQuantile u a + (∫ t in a..b, (profileValue u t)⁻¹) =
    rawQuantile u b at hadd
  linarith

theorem profileVariance_pos {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) : 0 < profileVariance u := by
  let q₁ : ℝ := 1 / 4
  let q₂ : ℝ := 3 / 4
  have hq₁ : q₁ ∈ Ioo (0 : ℝ) 1 := by dsimp [q₁]; norm_num
  have hq₂ : q₂ ∈ Ioo (0 : ℝ) 1 := by dsimp [q₂]; norm_num
  have hlt : rawQuantile u q₁ < rawQuantile u q₂ :=
    strictMonoOn_rawQuantile hu hq₁ hq₂ (by dsimp [q₁, q₂]; norm_num)
  have hne : centeredQuantile u q₁ ≠ 0 ∨ centeredQuantile u q₂ ≠ 0 := by
    by_contra h
    push Not at h
    dsimp [centeredQuantile] at h
    linarith
  obtain ⟨q, hq, hqne⟩ : ∃ q ∈ Ioo (0 : ℝ) 1, centeredQuantile u q ≠ 0 := by
    rcases hne with hne | hne
    · exact ⟨q₁, hq₁, hne⟩
    · exact ⟨q₂, hq₂, hne⟩
  have hcont : ContinuousAt (centeredQuantile u) q := by
    have hraw := continuousOn_rawQuantile_Ioo hu q hq
    exact (hraw.continuousAt (Ioo_mem_nhds hq.1 hq.2)).sub continuousAt_const
  have hsupp : Function.support (centeredQuantile u) ∈ nhds q := by
    have hz : ({0} : Set ℝ)ᶜ ∈ nhds (centeredQuantile u q) :=
      isOpen_compl_singleton.mem_nhds (by simpa [Set.mem_compl_iff] using hqne)
    change (centeredQuantile u) ⁻¹' ({0} : Set ℝ)ᶜ ∈ nhds q
    exact hcont hz
  have hIoc : Ioc (0 : ℝ) 1 ∈ nhds q :=
    Filter.mem_of_superset (Ioo_mem_nhds hq.1 hq.2) Ioo_subset_Ioc_self
  have hmeasure : 0 < volume (Function.support (fun t ↦ (centeredQuantile u t) ^ 2) ∩
      Ioc (0 : ℝ) 1) := by
    have hsuppSq : Function.support (fun t ↦ (centeredQuantile u t) ^ 2) =
        Function.support (centeredQuantile u) := by
      ext t
      simp [Function.mem_support]
    rw [hsuppSq]
    exact volume.measure_pos_of_mem_nhds (Filter.inter_mem hsupp hIoc)
  apply (intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    (f := fun t ↦ (centeredQuantile u t) ^ 2)
    (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
    (intervalIntegrable_centeredQuantile_sq hu)).2
  exact ⟨zero_lt_one, hmeasure⟩

def profileSigma (u : ProfileParam) : ℝ :=
  sqrt (profileVariance u)

theorem profileSigma_pos {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) : 0 < profileSigma u := by
  exact Real.sqrt_pos.2 (profileVariance_pos hu)

theorem continuousOn_profileSigma :
    ContinuousOn profileSigma normalizedProfiles := by
  exact continuousOn_profileVariance.sqrt

def standardizedQuantile (u : ProfileParam) (t : ℝ) : ℝ :=
  centeredQuantile u t / profileSigma u

def profileObjective (alpha : ℝ) (u : ProfileParam) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    LogConcaveClaimI.gAlpha alpha (standardizedQuantile u t)

theorem continuousOn_standardizedQuantile_at {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    ContinuousOn (fun u : ProfileParam ↦ standardizedQuantile u t)
      normalizedProfiles := by
  intro u hu
  have hcent : ContinuousWithinAt (fun v : ProfileParam ↦ centeredQuantile v t)
      normalizedProfiles u :=
    (continuousOn_rawQuantile_at ht u hu).sub (continuousOn_profileMean u hu)
  have hsigma := continuousOn_profileSigma u hu
  exact hcent.div hsigma (profileSigma_pos hu).ne'

theorem aestronglyMeasurable_standardizedQuantile_Ioc {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) :
    AEStronglyMeasurable (standardizedQuantile u)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hm := aestronglyMeasurable_rawQuantile_Ioc hu
  have hcenter : AEStronglyMeasurable (centeredQuantile u)
      (volume.restrict (Ioc (0 : ℝ) 1)) := hm.sub aestronglyMeasurable_const
  have hmul : AEStronglyMeasurable
      (fun t ↦ centeredQuantile u t * (profileSigma u)⁻¹)
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    exact (hcenter.mul_const (profileSigma u)⁻¹).congr
      (Filter.Eventually.of_forall (fun _ ↦ rfl))
  change AEStronglyMeasurable
    (fun t ↦ centeredQuantile u t / profileSigma u)
    (volume.restrict (Ioc (0 : ℝ) 1))
  simpa only [div_eq_mul_inv] using hmul

/-- The standardized profile objective is continuous on the compact profile
space.  The nonnegativity assumption is used only for the uniform bound
`|gα| ≤ 1`. -/
theorem continuousOn_profileObjective (alpha : ℝ) (halpha : 0 ≤ alpha) :
    ContinuousOn (profileObjective alpha) normalizedProfiles := by
  intro u hu
  apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (F := fun v t ↦ LogConcaveClaimI.gAlpha alpha (standardizedQuantile v t))
      (bound := fun _ ↦ (1 : ℝ))
  · filter_upwards [self_mem_nhdsWithin] with v hv
    have hstd := aestronglyMeasurable_standardizedQuantile_Ioc hv
    have hg : AEStronglyMeasurable
        (fun t ↦ LogConcaveClaimI.gAlpha alpha (standardizedQuantile v t))
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      (LogConcaveClaimI.continuous_gAlpha alpha).comp_aestronglyMeasurable hstd
    simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hg
  · filter_upwards [self_mem_nhdsWithin] with v hv
    filter_upwards with t
    intro _
    exact LogConcaveClaimI.abs_gAlpha_le_one halpha _
  · exact intervalIntegrable_const
  · have hnull : volume ({1} : Set ℝ) = 0 := by simp
    filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht1
    intro ht
    have ht1' : t ≠ 1 := by simpa using ht1
    have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
      simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
    have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨htIoc.1, htIoc.2.lt_of_ne ht1'⟩
    exact (LogConcaveClaimI.continuous_gAlpha alpha).continuousAt.comp_continuousWithinAt
      (continuousOn_standardizedQuantile_at htI u hu)

/-! ## Extensionality on the open quantile interval -/

theorem rawQuantile_eq_of_profileValue_eq {u v : ProfileParam}
    (hprofile : ∀ t ∈ Ioo (0 : ℝ) 1, profileValue u t = profileValue v t)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    rawQuantile u t = rawQuantile v t := by
  apply intervalIntegral.integral_congr
  intro s hs
  have hsI : s ∈ Ioo (0 : ℝ) 1 := by
    rcases mem_uIcc.mp hs with hs | hs
    · exact ⟨(by linarith), hs.2.trans_lt ht.2⟩
    · exact ⟨ht.1.trans_le hs.1, by linarith⟩
  change (profileValue u s)⁻¹ = (profileValue v s)⁻¹
  rw [hprofile s hsI]

theorem profileMean_eq_of_profileValue_eq {u v : ProfileParam}
    (hprofile : ∀ t ∈ Ioo (0 : ℝ) 1, profileValue u t = profileValue v t) :
    profileMean u = profileMean v := by
  apply intervalIntegral.integral_congr_ae
  have hnull : volume ({1} : Set ℝ) = 0 := by simp
  filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht1
  intro ht
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
    simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
  have ht1' : t ≠ 1 := by simpa using ht1
  exact rawQuantile_eq_of_profileValue_eq hprofile ⟨htIoc.1, htIoc.2.lt_of_ne ht1'⟩

theorem centeredQuantile_eq_of_profileValue_eq {u v : ProfileParam}
    (hprofile : ∀ t ∈ Ioo (0 : ℝ) 1, profileValue u t = profileValue v t)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    centeredQuantile u t = centeredQuantile v t := by
  rw [centeredQuantile, centeredQuantile,
    rawQuantile_eq_of_profileValue_eq hprofile ht,
    profileMean_eq_of_profileValue_eq hprofile]

theorem profileVariance_eq_of_profileValue_eq {u v : ProfileParam}
    (hprofile : ∀ t ∈ Ioo (0 : ℝ) 1, profileValue u t = profileValue v t) :
    profileVariance u = profileVariance v := by
  apply intervalIntegral.integral_congr_ae
  have hnull : volume ({1} : Set ℝ) = 0 := by simp
  filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht1
  intro ht
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
    simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
  have ht1' : t ≠ 1 := by simpa using ht1
  rw [centeredQuantile_eq_of_profileValue_eq hprofile
    ⟨htIoc.1, htIoc.2.lt_of_ne ht1'⟩]

theorem profileSigma_eq_of_profileValue_eq {u v : ProfileParam}
    (hprofile : ∀ t ∈ Ioo (0 : ℝ) 1, profileValue u t = profileValue v t) :
    profileSigma u = profileSigma v := by
  rw [profileSigma, profileSigma, profileVariance_eq_of_profileValue_eq hprofile]

theorem standardizedQuantile_eq_of_profileValue_eq {u v : ProfileParam}
    (hprofile : ∀ t ∈ Ioo (0 : ℝ) 1, profileValue u t = profileValue v t)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    standardizedQuantile u t = standardizedQuantile v t := by
  rw [standardizedQuantile, standardizedQuantile,
    centeredQuantile_eq_of_profileValue_eq hprofile ht,
    profileSigma_eq_of_profileValue_eq hprofile]

theorem profileObjective_eq_of_profileValue_eq (alpha : ℝ) {u v : ProfileParam}
    (hprofile : ∀ t ∈ Ioo (0 : ℝ) 1, profileValue u t = profileValue v t) :
    profileObjective alpha u = profileObjective alpha v := by
  apply intervalIntegral.integral_congr_ae
  have hnull : volume ({1} : Set ℝ) = 0 := by simp
  filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht1
  intro ht
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
    simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
  have ht1' : t ≠ 1 := by simpa using ht1
  rw [standardizedQuantile_eq_of_profileValue_eq hprofile
    ⟨htIoc.1, htIoc.2.lt_of_ne ht1'⟩]

end LogConcaveFamily6.ProfileCompactification

end FlattenedExistenceSection5


/-!
Flattened source section: ProfileEndpointReduction.lean
-/

section FlattenedExistenceSection6

/-!
# Removing collapsed kink-mass endpoints

At `p = 0` or `p = 1`, one branch of the four-coordinate profile is
collapsed.  The same piecewise-affine function on `(0,1)` can be represented
with kink mass `1/2`.  This small reparametrization lets the decoder work only
with a genuine interior kink mass, without changing any reconstructed
quantile or standardized objective.
-/



open Real Set

namespace LogConcaveFamily6.ProfileCompactification

/-- Replace a collapsed kink mass by an artificial kink at `1/2` on the same
affine segment. -/
def interiorizeKinkMass (u : ProfileParam) : ProfileParam :=
  if kinkMass u = 0 then
    ![(1 / 2 : ℝ), kinkValue u,
      (kinkValue u + rightValue u) / 2, rightValue u]
  else if kinkMass u = 1 then
    ![(1 / 2 : ℝ), leftValue u,
      (leftValue u + kinkValue u) / 2, kinkValue u]
  else u

@[simp] theorem kinkMass_interiorizeKinkMass_of_zero
    {u : ProfileParam} (hp : kinkMass u = 0) :
    kinkMass (interiorizeKinkMass u) = 1 / 2 := by
  change u 0 = 0 at hp
  simp [interiorizeKinkMass, hp, kinkMass]

@[simp] theorem kinkMass_interiorizeKinkMass_of_one
    {u : ProfileParam} (hp : kinkMass u = 1) :
    kinkMass (interiorizeKinkMass u) = 1 / 2 := by
  change u 0 = 1 at hp
  simp [interiorizeKinkMass, hp, kinkMass]

theorem kinkMass_interiorizeKinkMass_pos {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) :
    0 < kinkMass (interiorizeKinkMass u) := by
  by_cases hp0 : kinkMass u = 0
  · rw [kinkMass_interiorizeKinkMass_of_zero hp0]
    norm_num
  by_cases hp1 : kinkMass u = 1
  · rw [kinkMass_interiorizeKinkMass_of_one hp1]
    norm_num
  · simp only [interiorizeKinkMass, hp0, hp1, if_false]
    exact lt_of_le_of_ne (kinkMass_nonneg hu) (Ne.symm hp0)

theorem kinkMass_interiorizeKinkMass_lt_one {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) :
    kinkMass (interiorizeKinkMass u) < 1 := by
  by_cases hp0 : kinkMass u = 0
  · rw [kinkMass_interiorizeKinkMass_of_zero hp0]
    norm_num
  by_cases hp1 : kinkMass u = 1
  · rw [kinkMass_interiorizeKinkMass_of_one hp1]
    norm_num
  · simp only [interiorizeKinkMass, hp0, hp1, if_false]
    exact lt_of_le_of_ne (kinkMass_le_one hu) hp1

lemma max_kink_right_eq_one_of_kinkMass_eq_zero {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) (hp : kinkMass u = 0) :
    max (kinkValue u) (rightValue u) = 1 := by
  have hc := profile_concavity hu
  have hn := hu.2.2
  rw [hp] at hc
  change max (leftValue u) (max (kinkValue u) (rightValue u)) = 1 at hn
  have hlh : leftValue u ≤ kinkValue u := by nlinarith
  rw [max_eq_right (hlh.trans (le_max_left _ _))] at hn
  exact hn

lemma max_left_kink_eq_one_of_kinkMass_eq_one {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) (hp : kinkMass u = 1) :
    max (leftValue u) (kinkValue u) = 1 := by
  have hc := profile_concavity hu
  have hn := hu.2.2
  rw [hp] at hc
  change max (leftValue u) (max (kinkValue u) (rightValue u)) = 1 at hn
  have hrh : rightValue u ≤ kinkValue u := by nlinarith
  rw [max_eq_left hrh] at hn
  exact hn

/-- Endpoint interiorization preserves the compact normalized profile set. -/
theorem interiorizeKinkMass_mem {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) :
    interiorizeKinkMass u ∈ normalizedProfiles := by
  by_cases hp0 : kinkMass u = 0
  · have hh0 := kinkValue_nonneg hu
    have hh1 := kinkValue_le_one hu
    have hr0 := rightValue_nonneg hu
    have hr1 := rightValue_le_one hu
    have hmax := max_kink_right_eq_one_of_kinkMass_eq_zero hu hp0
    rw [interiorizeKinkMass, if_pos hp0]
    constructor
    · intro i _
      fin_cases i
      · norm_num
      · exact ⟨hh0, hh1⟩
      · change 0 ≤ (kinkValue u + rightValue u) / 2 ∧
          (kinkValue u + rightValue u) / 2 ≤ 1
        constructor <;> nlinarith
      · exact ⟨hr0, hr1⟩
    · constructor
      · change (1 - (1 / 2 : ℝ)) * kinkValue u +
          (1 / 2 : ℝ) * rightValue u ≤
            (kinkValue u + rightValue u) / 2
        nlinarith
      · change max (kinkValue u)
          (max ((kinkValue u + rightValue u) / 2) (rightValue u)) = 1
        rcases le_total (kinkValue u) (rightValue u) with hhr | hrh
        · rw [max_eq_right hhr] at hmax
          have hmid : (kinkValue u + rightValue u) / 2 ≤ rightValue u := by
            linarith
          rw [max_eq_right hmid, max_eq_right hhr, hmax]
        · rw [max_eq_left hrh] at hmax
          have hmid : (kinkValue u + rightValue u) / 2 ≤ kinkValue u := by
            linarith
          have hinner : max ((kinkValue u + rightValue u) / 2)
              (rightValue u) ≤ kinkValue u := max_le hmid hrh
          rw [max_eq_left hinner, hmax]
  by_cases hp1 : kinkMass u = 1
  · have hl0 := leftValue_nonneg hu
    have hl1 := leftValue_le_one hu
    have hh0 := kinkValue_nonneg hu
    have hh1 := kinkValue_le_one hu
    have hmax := max_left_kink_eq_one_of_kinkMass_eq_one hu hp1
    rw [interiorizeKinkMass, if_neg hp0, if_pos hp1]
    constructor
    · intro i _
      fin_cases i
      · norm_num
      · exact ⟨hl0, hl1⟩
      · change 0 ≤ (leftValue u + kinkValue u) / 2 ∧
          (leftValue u + kinkValue u) / 2 ≤ 1
        constructor <;> nlinarith
      · exact ⟨hh0, hh1⟩
    · constructor
      · change (1 - (1 / 2 : ℝ)) * leftValue u +
          (1 / 2 : ℝ) * kinkValue u ≤
            (leftValue u + kinkValue u) / 2
        nlinarith
      · change max (leftValue u)
          (max ((leftValue u + kinkValue u) / 2) (kinkValue u)) = 1
        rcases le_total (leftValue u) (kinkValue u) with hlh | hhl
        · rw [max_eq_right hlh] at hmax
          have hmid : (leftValue u + kinkValue u) / 2 ≤ kinkValue u := by
            linarith
          rw [max_eq_right hmid, max_eq_right hlh, hmax]
        · rw [max_eq_left hhl] at hmax
          have hmid : (leftValue u + kinkValue u) / 2 ≤ leftValue u := by
            linarith
          have hinner : max ((leftValue u + kinkValue u) / 2)
              (kinkValue u) ≤ leftValue u := max_le hmid hhl
          rw [max_eq_left hinner, hmax]
  · simpa [interiorizeKinkMass, hp0, hp1] using hu

/-- The actual profile function is unchanged at every interior probability
level. -/
theorem profileValue_interiorizeKinkMass {u : ProfileParam}
    (hu : u ∈ normalizedProfiles) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    profileValue (interiorizeKinkMass u) t = profileValue u t := by
  by_cases hp0 : kinkMass u = 0
  · have hp0' : u 0 = 0 := hp0
    by_cases htH : t ≤ (1 / 2 : ℝ)
    · simp [interiorizeKinkMass, profileValue, kinkMass, leftValue,
        kinkValue, rightValue, hp0', htH, not_le_of_gt ht.1] <;>
        split <;> ring_nf
    · simp [interiorizeKinkMass, profileValue, kinkMass, leftValue,
        kinkValue, rightValue, hp0', htH, not_le_of_gt ht.1] <;>
        split <;> ring_nf
  by_cases hp1 : kinkMass u = 1
  · have hp0' : u 0 ≠ 0 := hp0
    have hp1' : u 0 = 1 := hp1
    by_cases htH : t ≤ (1 / 2 : ℝ)
    · simp [interiorizeKinkMass, profileValue, kinkMass, leftValue,
        kinkValue, rightValue, hp0', hp1', htH, ht.2.le] <;>
        split <;> ring_nf
    · simp [interiorizeKinkMass, profileValue, kinkMass, leftValue,
        kinkValue, rightValue, hp0', hp1', htH, ht.2.le] <;>
        split <;> ring_nf
  · simp [interiorizeKinkMass, hp0, hp1]

/-- Collapsed-kink interiorization does not change the standardized profile
objective. -/
theorem profileObjective_interiorizeKinkMass (alpha : ℝ)
    {u : ProfileParam} (hu : u ∈ normalizedProfiles) :
    profileObjective alpha (interiorizeKinkMass u) = profileObjective alpha u := by
  apply profileObjective_eq_of_profileValue_eq alpha
  intro t ht
  exact profileValue_interiorizeKinkMass hu ht

end LogConcaveFamily6.ProfileCompactification

end FlattenedExistenceSection6


/-!
Flattened source section: ProfileDecode.lean
-/

section FlattenedExistenceSection7

/-!
# Affine normalization for the compact chart of family (6)

This file supplies the change-of-variables part of the normalized-profile
decoder.  It is deliberately stated for an arbitrary compact two-piece
exponential density: translating and rescaling the random variable stays in
the same chart, and all tagged integrals transform exactly.
-/



open Real Set MeasureTheory intervalIntegral
open scoped Interval

namespace LogConcaveFamily6.ProfileDecode

open LogConcaveClaimI

/-- Parameters of the density of `(X - mu) / sigma`, when `X` has compact
family-(6) parameter `p` and `sigma > 0`. -/
def affineCompact (p : CompactParam) (mu sigma : ℝ) : CompactParam :=
  ![(p 0 - mu) / sigma,
    (p 1 - mu) / sigma,
    Real.log sigma + p 2 + p 3 * mu,
    p 3 * sigma,
    p 4 * sigma,
    (p 5 - mu) / sigma]

@[simp] lemma affineCompact_zero (p : CompactParam) (mu sigma : ℝ) :
    affineCompact p mu sigma 0 = (p 0 - mu) / sigma := rfl

@[simp] lemma affineCompact_one (p : CompactParam) (mu sigma : ℝ) :
    affineCompact p mu sigma 1 = (p 1 - mu) / sigma := rfl

@[simp] lemma affineCompact_two (p : CompactParam) (mu sigma : ℝ) :
    affineCompact p mu sigma 2 = Real.log sigma + p 2 + p 3 * mu := rfl

@[simp] lemma affineCompact_three (p : CompactParam) (mu sigma : ℝ) :
    affineCompact p mu sigma 3 = p 3 * sigma := rfl

@[simp] lemma affineCompact_four (p : CompactParam) (mu sigma : ℝ) :
    affineCompact p mu sigma 4 = p 4 * sigma := rfl

@[simp] lemma affineCompact_five (p : CompactParam) (mu sigma : ℝ) :
    affineCompact p mu sigma 5 = (p 5 - mu) / sigma := rfl

lemma affineCompact_leftExponent
    (p : CompactParam) (mu sigma y : ℝ) (hsigma : 0 < sigma) :
    exp (leftExponent (affineCompact p mu sigma) y) =
      sigma * exp (leftExponent p (sigma * y + mu)) := by
  rw [leftExponent, affineCompact_two, affineCompact_three, leftExponent]
  calc
    exp (log sigma + p 2 + p 3 * mu + p 3 * sigma * y) =
        exp (log sigma + (p 2 + p 3 * (sigma * y + mu))) := by
          congr 1
          ring
    _ = exp (log sigma) * exp (p 2 + p 3 * (sigma * y + mu)) :=
      Real.exp_add _ _
    _ = sigma * exp (p 2 + p 3 * (sigma * y + mu)) := by
      rw [Real.exp_log hsigma]

lemma affineCompact_rightExponent
    (p : CompactParam) (mu sigma y : ℝ) (hsigma : 0 < sigma) :
    exp (rightExponent (affineCompact p mu sigma) y) =
      sigma * exp (rightExponent p (sigma * y + mu)) := by
  rw [rightExponent, affineCompact_two, affineCompact_three,
    affineCompact_four, affineCompact_five, rightExponent]
  have hexponent :
      log sigma + p 2 + p 3 * mu + p 3 * sigma * y -
          p 4 * sigma * (y - (p 5 - mu) / sigma) =
        log sigma + (p 2 + p 3 * (sigma * y + mu) -
          p 4 * (sigma * y + mu - p 5)) := by
    field_simp [ne_of_gt hsigma]
    ring
  rw [hexponent, Real.exp_add, Real.exp_log hsigma]

/-- Exact positive affine change of variables on the left compact piece. -/
lemma affineCompact_leftIntegral
    (q : ℝ → ℝ) (p : CompactParam) (mu sigma : ℝ)
    (hsigma : 0 < sigma) :
    leftIntegral q (affineCompact p mu sigma) =
      leftIntegral (fun x ↦ q ((x - mu) / sigma)) p := by
  unfold leftIntegral leftIntegrand
  simp only [affineCompact_zero, affineCompact_five]
  have hcv := intervalIntegral.mul_integral_comp_mul_add
    (f := fun x : ℝ ↦ q ((x - mu) / sigma) * exp (leftExponent p x))
    (a := (p 0 - mu) / sigma) (b := (p 5 - mu) / sigma) sigma mu
  rw [show sigma * ((p 0 - mu) / sigma) + mu = p 0 by
      field_simp [ne_of_gt hsigma]; ring,
    show sigma * ((p 5 - mu) / sigma) + mu = p 5 by
      field_simp [ne_of_gt hsigma]; ring] at hcv
  rw [← hcv]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  change q y * exp (leftExponent (affineCompact p mu sigma) y) =
    sigma * (q ((sigma * y + mu - mu) / sigma) *
      exp (leftExponent p (sigma * y + mu)))
  rw [affineCompact_leftExponent p mu sigma y hsigma]
  have harg : (sigma * y + mu - mu) / sigma = y := by
    field_simp [ne_of_gt hsigma]
    ring
  rw [harg]
  ring

/-- Exact positive affine change of variables on the right compact piece. -/
lemma affineCompact_rightIntegral
    (q : ℝ → ℝ) (p : CompactParam) (mu sigma : ℝ)
    (hsigma : 0 < sigma) :
    rightIntegral q (affineCompact p mu sigma) =
      rightIntegral (fun x ↦ q ((x - mu) / sigma)) p := by
  unfold rightIntegral rightIntegrand
  simp only [affineCompact_one, affineCompact_five]
  have hcv := intervalIntegral.mul_integral_comp_mul_add
    (f := fun x : ℝ ↦ q ((x - mu) / sigma) * exp (rightExponent p x))
    (a := (p 5 - mu) / sigma) (b := (p 1 - mu) / sigma) sigma mu
  rw [show sigma * ((p 5 - mu) / sigma) + mu = p 5 by
      field_simp [ne_of_gt hsigma]; ring,
    show sigma * ((p 1 - mu) / sigma) + mu = p 1 by
      field_simp [ne_of_gt hsigma]; ring] at hcv
  rw [← hcv]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  change q y * exp (rightExponent (affineCompact p mu sigma) y) =
    sigma * (q ((sigma * y + mu - mu) / sigma) *
      exp (rightExponent p (sigma * y + mu)))
  rw [affineCompact_rightExponent p mu sigma y hsigma]
  have harg : (sigma * y + mu - mu) / sigma = y := by
    field_simp [ne_of_gt hsigma]
    ring
  rw [harg]
  ring

/-- Exact transformation law for every tagged compact integral. -/
theorem affineCompact_integral
    (q : ℝ → ℝ) (p : CompactParam) (mu sigma : ℝ)
    (hsigma : 0 < sigma) :
    compactIntegral q (affineCompact p mu sigma) =
      compactIntegral (fun x ↦ q ((x - mu) / sigma)) p := by
  unfold compactIntegral
  rw [affineCompact_leftIntegral q p mu sigma hsigma,
    affineCompact_rightIntegral q p mu sigma hsigma]

/-- Positive affine normalization preserves the compact chart inequalities. -/
theorem affineCompact_admissible
    {p : CompactParam} {mu sigma : ℝ}
    (hp : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hsigma : 0 < sigma) :
    (affineCompact p mu sigma) 0 < (affineCompact p mu sigma) 5 ∧
      (affineCompact p mu sigma) 5 < (affineCompact p mu sigma) 1 ∧
      0 ≤ (affineCompact p mu sigma) 4 := by
  simp only [affineCompact_zero, affineCompact_one, affineCompact_four,
    affineCompact_five]
  constructor
  · exact (div_lt_div_iff_of_pos_right hsigma).2 (sub_lt_sub_right hp.1 mu)
  constructor
  · exact (div_lt_div_iff_of_pos_right hsigma).2 (sub_lt_sub_right hp.2.1 mu)
  · exact mul_nonneg hp.2.2 hsigma.le

/-! ## Moment normalization -/

lemma compactIntegral_congr {q r : ℝ → ℝ} (p : CompactParam)
    (hqr : ∀ x, q x = r x) : compactIntegral q p = compactIntegral r p := by
  unfold compactIntegral leftIntegral rightIntegral leftIntegrand rightIntegrand
  congr 1 <;> apply intervalIntegral.integral_congr <;> intro x _
  · change q x * exp (leftExponent p x) = r x * exp (leftExponent p x)
    rw [hqr x]
  · change q x * exp (rightExponent p x) = r x * exp (rightExponent p x)
    rw [hqr x]

lemma compactIntegral_linear
    (p : CompactParam) (a b : ℝ) (q r : ℝ → ℝ)
    (hq : Continuous q) (hr : Continuous r) :
    compactIntegral (fun x ↦ a * q x + b * r x) p =
      a * compactIntegral q p + b * compactIntegral r p := by
  have hqL : IntervalIntegrable
      (fun x ↦ q x * exp (leftExponent p x)) volume (p 0) (p 5) :=
    (hq.mul (continuous_compactLeftWeight p)).intervalIntegrable _ _
  have hrL : IntervalIntegrable
      (fun x ↦ r x * exp (leftExponent p x)) volume (p 0) (p 5) :=
    (hr.mul (continuous_compactLeftWeight p)).intervalIntegrable _ _
  have hqR : IntervalIntegrable
      (fun x ↦ q x * exp (rightExponent p x)) volume (p 5) (p 1) :=
    (hq.mul (continuous_compactRightWeight p)).intervalIntegrable _ _
  have hrR : IntervalIntegrable
      (fun x ↦ r x * exp (rightExponent p x)) volume (p 5) (p 1) :=
    (hr.mul (continuous_compactRightWeight p)).intervalIntegrable _ _
  unfold compactIntegral leftIntegral rightIntegral leftIntegrand rightIntegrand
  have hleft :
      (∫ x in p 0..p 5,
          (a * q x + b * r x) * exp (leftExponent p x)) =
        a * (∫ x in p 0..p 5, q x * exp (leftExponent p x)) +
          b * (∫ x in p 0..p 5, r x * exp (leftExponent p x)) := by
    calc
      _ = ∫ x in p 0..p 5,
          a * (q x * exp (leftExponent p x)) +
            b * (r x * exp (leftExponent p x)) := by
              apply intervalIntegral.integral_congr
              intro x _
              ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hqL.const_mul a) (hrL.const_mul b),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  have hright :
      (∫ x in p 5..p 1,
          (a * q x + b * r x) * exp (rightExponent p x)) =
        a * (∫ x in p 5..p 1, q x * exp (rightExponent p x)) +
          b * (∫ x in p 5..p 1, r x * exp (rightExponent p x)) := by
    calc
      _ = ∫ x in p 5..p 1,
          a * (q x * exp (rightExponent p x)) +
            b * (r x * exp (rightExponent p x)) := by
              apply intervalIntegral.integral_congr
              intro x _
              ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hqR.const_mul a) (hrR.const_mul b),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
  rw [hleft, hright]
  ring

/-- Affine normalization sends mass to mass. -/
theorem affineCompact_mass
    (p : CompactParam) (mu sigma : ℝ) (hsigma : 0 < sigma) :
    compactIntegral (fun _ : ℝ ↦ 1) (affineCompact p mu sigma) =
      compactIntegral (fun _ : ℝ ↦ 1) p := by
  simpa using
    (affineCompact_integral (fun _ : ℝ ↦ 1) p mu sigma hsigma)

/-- Affine normalization sends the first moment to
`(first moment - mu * mass) / sigma`. -/
theorem affineCompact_firstMoment
    (p : CompactParam) (mu sigma : ℝ) (hsigma : 0 < sigma) :
    compactIntegral (fun x : ℝ ↦ x) (affineCompact p mu sigma) =
      (compactIntegral (fun x : ℝ ↦ x) p -
        mu * compactIntegral (fun _ : ℝ ↦ 1) p) / sigma := by
  rw [affineCompact_integral (fun x : ℝ ↦ x) p mu sigma hsigma]
  calc
    compactIntegral (fun x ↦ (x - mu) / sigma) p =
        compactIntegral
          (fun x ↦ sigma⁻¹ * x + (-mu * sigma⁻¹) * 1) p := by
      apply compactIntegral_congr
      intro x
      field_simp [ne_of_gt hsigma]
      ring
    _ = sigma⁻¹ * compactIntegral (fun x : ℝ ↦ x) p +
        (-mu * sigma⁻¹) * compactIntegral (fun _ : ℝ ↦ 1) p := by
      rw [compactIntegral_linear p sigma⁻¹ (-mu * sigma⁻¹)
        (fun x : ℝ ↦ x) (fun _ : ℝ ↦ 1) continuous_id continuous_const]
    _ = _ := by
      field_simp [ne_of_gt hsigma]
      ring

/-- Affine normalization sends the second moment by the usual quadratic
formula. -/
theorem affineCompact_secondMoment
    (p : CompactParam) (mu sigma : ℝ) (hsigma : 0 < sigma) :
    compactIntegral (fun x : ℝ ↦ x ^ 2) (affineCompact p mu sigma) =
      (compactIntegral (fun x : ℝ ↦ x ^ 2) p -
          2 * mu * compactIntegral (fun x : ℝ ↦ x) p +
          mu ^ 2 * compactIntegral (fun _ : ℝ ↦ 1) p) /
        sigma ^ 2 := by
  rw [affineCompact_integral (fun x : ℝ ↦ x ^ 2) p mu sigma hsigma]
  have hs2 : sigma ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hsigma)
  calc
    compactIntegral (fun x ↦ ((x - mu) / sigma) ^ 2) p =
        compactIntegral
          (fun x ↦ (sigma ^ 2)⁻¹ * x ^ 2 +
            ((-2 * mu) * (sigma ^ 2)⁻¹) * x +
            (mu ^ 2 * (sigma ^ 2)⁻¹) * 1) p := by
      apply compactIntegral_congr
      intro x
      field_simp [hs2]
      ring
    _ = compactIntegral
          (fun x ↦ (sigma ^ 2)⁻¹ * x ^ 2 +
            ((-2 * mu) * (sigma ^ 2)⁻¹) * x) p +
          (mu ^ 2 * (sigma ^ 2)⁻¹) *
            compactIntegral (fun _ : ℝ ↦ 1) p := by
      rw [compactIntegral_congr (p := p)
        (q := fun x ↦ (sigma ^ 2)⁻¹ * x ^ 2 +
          ((-2 * mu) * (sigma ^ 2)⁻¹) * x +
          (mu ^ 2 * (sigma ^ 2)⁻¹) * 1)
        (r := fun x ↦ 1 * ((sigma ^ 2)⁻¹ * x ^ 2 +
          ((-2 * mu) * (sigma ^ 2)⁻¹) * x) +
          (mu ^ 2 * (sigma ^ 2)⁻¹) * 1) (by intro x; ring),
        compactIntegral_linear p 1 (mu ^ 2 * (sigma ^ 2)⁻¹)
        (fun x ↦ (sigma ^ 2)⁻¹ * x ^ 2 +
          ((-2 * mu) * (sigma ^ 2)⁻¹) * x)
        (fun _ : ℝ ↦ 1) (by fun_prop) continuous_const]
      ring
    _ = ((sigma ^ 2)⁻¹ * compactIntegral (fun x : ℝ ↦ x ^ 2) p +
          ((-2 * mu) * (sigma ^ 2)⁻¹) *
            compactIntegral (fun x : ℝ ↦ x) p) +
          (mu ^ 2 * (sigma ^ 2)⁻¹) *
            compactIntegral (fun _ : ℝ ↦ 1) p := by
      rw [compactIntegral_linear p (sigma ^ 2)⁻¹
        ((-2 * mu) * (sigma ^ 2)⁻¹)
        (fun x : ℝ ↦ x ^ 2) (fun x : ℝ ↦ x)
        (continuous_id.pow 2) continuous_id]
    _ = _ := by
      field_simp [hs2]
      ring

/-- A mass-one compact density becomes isotropic after centering at its raw
mean and scaling by the positive square root of its raw variance. -/
theorem affineCompact_isIsotropic
    {p : CompactParam} {mu sigma : ℝ}
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1)
    (hmean : compactIntegral (fun x : ℝ ↦ x) p = mu)
    (hsecond : compactIntegral (fun x : ℝ ↦ x ^ 2) p = mu ^ 2 + sigma ^ 2)
    (hsigma : 0 < sigma) :
    LogConcaveFamily6.IsIsotropic (.compact (affineCompact p mu sigma)) := by
  funext k
  fin_cases k
  · simp only [LogConcaveFamily6.momentMap, LogConcaveFamily6.integral,
      LogConcaveFamily6.isotropicTarget, pow_zero, if_pos]
    change compactIntegral (fun _ : ℝ ↦ 1)
        (affineCompact p mu sigma) = 1
    rw [affineCompact_mass p mu sigma hsigma, hmass]
  · simp only [LogConcaveFamily6.momentMap, LogConcaveFamily6.integral,
      LogConcaveFamily6.isotropicTarget, pow_one]
    change compactIntegral (fun x : ℝ ↦ x)
        (affineCompact p mu sigma) = 0
    rw [affineCompact_firstMoment p mu sigma hsigma, hmean, hmass]
    field_simp [ne_of_gt hsigma]
    ring
  · simp only [LogConcaveFamily6.momentMap, LogConcaveFamily6.integral,
      LogConcaveFamily6.isotropicTarget]
    change compactIntegral (fun x : ℝ ↦ x ^ 2)
        (affineCompact p mu sigma) = 1
    rw [affineCompact_secondMoment p mu sigma hsigma,
      hsecond, hmean, hmass]
    field_simp [pow_ne_zero 2 (ne_of_gt hsigma)]
    ring

/-! ## Interior raw profile decoder -/

/-- A strictly interior normalized-profile shape.  Normalization of
`max {l,h,r}` is irrelevant for reconstruction, so it is intentionally not
included here. -/
structure InteriorProfile where
  p : ℝ
  l : ℝ
  h : ℝ
  r : ℝ
  p_pos : 0 < p
  p_lt_one : p < 1
  l_pos : 0 < l
  h_pos : 0 < h
  r_pos : 0 < r
  concave : (1 - p) * l + p * r ≤ h

def leftSlope (u : InteriorProfile) : ℝ := (u.h - u.l) / u.p

def rightSlope (u : InteriorProfile) : ℝ :=
  (u.r - u.h) / (1 - u.p)

def leftLength (u : InteriorProfile) : ℝ :=
  if leftSlope u = 0 then u.p / u.l
  else log (u.h / u.l) / leftSlope u

def rightLength (u : InteriorProfile) : ℝ :=
  if rightSlope u = 0 then (1 - u.p) / u.h
  else log (u.r / u.h) / rightSlope u

/-- Raw compact parameter with left endpoint zero.  Its left and right
pieces have probability masses `p` and `1-p`; it is standardized below. -/
def rawCompact (u : InteriorProfile) : CompactParam :=
  ![0,
    leftLength u + rightLength u,
    log u.l,
    leftSlope u,
    leftSlope u - rightSlope u,
    leftLength u]

@[simp] lemma rawCompact_zero (u : InteriorProfile) : rawCompact u 0 = 0 := rfl
@[simp] lemma rawCompact_one (u : InteriorProfile) :
    rawCompact u 1 = leftLength u + rightLength u := rfl
@[simp] lemma rawCompact_two (u : InteriorProfile) :
    rawCompact u 2 = log u.l := rfl
@[simp] lemma rawCompact_three (u : InteriorProfile) :
    rawCompact u 3 = leftSlope u := rfl
@[simp] lemma rawCompact_four (u : InteriorProfile) :
    rawCompact u 4 = leftSlope u - rightSlope u := rfl
@[simp] lemma rawCompact_five (u : InteriorProfile) :
    rawCompact u 5 = leftLength u := rfl

lemma rightSlope_le_leftSlope (u : InteriorProfile) :
    rightSlope u ≤ leftSlope u := by
  rw [rightSlope, leftSlope]
  apply (div_le_div_iff₀ (sub_pos.mpr u.p_lt_one) u.p_pos).2
  nlinarith [u.concave]

/-- Elementary antiderivative for an exponential affine function. -/
lemma integral_exp_affine_of_ne (c s a b : ℝ) (hs : s ≠ 0) :
    (∫ x in a..b, exp (c + s * x)) =
      (exp (c + s * b) - exp (c + s * a)) / s := by
  have hderiv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ ↦ exp (c + s * y) / s)
        (exp (c + s * x)) x := by
    intro x _
    have h := ((hasDerivAt_const x c).add
      ((hasDerivAt_id x).const_mul s)).exp.div_const s
    simpa [hs] using h
  have hint : IntervalIntegrable (fun x : ℝ ↦ exp (c + s * x)) volume a b :=
    (show Continuous (fun x : ℝ ↦ exp (c + s * x)) by fun_prop).intervalIntegrable _ _
  simpa [sub_div] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint)

lemma leftSlope_mul_p (u : InteriorProfile) :
    leftSlope u * u.p = u.h - u.l := by
  rw [leftSlope]
  field_simp [ne_of_gt u.p_pos]

lemma rightSlope_mul_one_sub_p (u : InteriorProfile) :
    rightSlope u * (1 - u.p) = u.r - u.h := by
  rw [rightSlope]
  field_simp [ne_of_gt (sub_pos.mpr u.p_lt_one)]

/-- The raw density takes the three prescribed profile values at the two
endpoints and the kink. -/
theorem rawCompact_leftEndpoint_value (u : InteriorProfile) :
    exp (leftExponent (rawCompact u) 0) = u.l := by
  simp [leftExponent, Real.exp_log u.l_pos]

theorem rawCompact_kink_value (u : InteriorProfile) :
    exp (leftExponent (rawCompact u) (leftLength u)) = u.h := by
  rw [leftExponent, rawCompact_two, rawCompact_three]
  unfold leftLength
  split_ifs with hs
  · have hhl : u.h = u.l := by
      have h := leftSlope_mul_p u
      rw [hs, zero_mul] at h
      linarith
    rw [hhl, hs]
    simp [Real.exp_log u.l_pos]
  · have hratio : 0 < u.h / u.l := div_pos u.h_pos u.l_pos
    have heq : log u.l + leftSlope u *
          (log (u.h / u.l) / leftSlope u) = log u.h := by
      field_simp [hs]
      rw [Real.log_div u.h_pos.ne' u.l_pos.ne']
      ring
    rw [heq, Real.exp_log u.h_pos]

theorem rawCompact_rightEndpoint_value (u : InteriorProfile) :
    exp (rightExponent (rawCompact u)
      (leftLength u + rightLength u)) = u.r := by
  have hkink :
      log u.l + leftSlope u * leftLength u = log u.h := by
    have hpos := rawCompact_kink_value u
    rw [leftExponent, rawCompact_two, rawCompact_three] at hpos
    rw [← Real.exp_log u.h_pos] at hpos
    exact Real.exp_injective hpos
  rw [rightExponent, rawCompact_two, rawCompact_three, rawCompact_four,
    rawCompact_five]
  have hexponent :
      log u.l + leftSlope u * (leftLength u + rightLength u) -
          (leftSlope u - rightSlope u) *
            (leftLength u + rightLength u - leftLength u) =
        log u.h + rightSlope u * rightLength u := by
    rw [← hkink]
    ring
  rw [hexponent]
  unfold rightLength
  split_ifs with hs
  · have hrh : u.r = u.h := by
      have h := rightSlope_mul_one_sub_p u
      rw [hs, zero_mul] at h
      linarith
    rw [hrh, hs]
    simp [Real.exp_log u.h_pos]
  · have heq : log u.h + rightSlope u *
          (log (u.r / u.h) / rightSlope u) = log u.r := by
      field_simp [hs]
      rw [Real.log_div u.r_pos.ne' u.h_pos.ne']
      ring
    rw [heq, Real.exp_log u.r_pos]

theorem rawCompact_left_mass (u : InteriorProfile) :
    leftIntegral (fun _ : ℝ ↦ 1) (rawCompact u) = u.p := by
  unfold leftIntegral leftIntegrand
  simp only [one_mul, rawCompact_zero, rawCompact_five]
  change (∫ x in 0..leftLength u, exp (log u.l + leftSlope u * x)) = u.p
  by_cases hs : leftSlope u = 0
  · have hhl : u.h = u.l := by
      have h := leftSlope_mul_p u
      rw [hs, zero_mul] at h
      linarith
    simp [leftExponent, leftLength, hs, Real.exp_log u.l_pos]
    field_simp [ne_of_gt u.l_pos]
  · rw [integral_exp_affine_of_ne (log u.l) (leftSlope u) 0
      (leftLength u) hs]
    have hk := rawCompact_kink_value u
    rw [leftExponent, rawCompact_two, rawCompact_three] at hk
    have hzero := rawCompact_leftEndpoint_value u
    rw [leftExponent, rawCompact_two, rawCompact_three] at hzero
    simp only [mul_zero, add_zero] at hzero
    simp only [mul_zero, add_zero]
    rw [hk, hzero]
    rw [div_eq_iff hs]
    simpa [mul_comm] using (leftSlope_mul_p u).symm

theorem rawCompact_right_mass (u : InteriorProfile) :
    rightIntegral (fun _ : ℝ ↦ 1) (rawCompact u) = 1 - u.p := by
  unfold rightIntegral rightIntegrand
  simp only [one_mul, rawCompact_five, rawCompact_one]
  have hkinkR :
      exp (rightExponent (rawCompact u) (leftLength u)) = u.h := by
    rw [rightExponent, rawCompact_two, rawCompact_three, rawCompact_four,
      rawCompact_five, sub_self, mul_zero, sub_zero]
    exact rawCompact_kink_value u
  by_cases hs : rightSlope u = 0
  · have hrh : u.r = u.h := by
      have h := rightSlope_mul_one_sub_p u
      rw [hs, zero_mul] at h
      linarith
    have hexp_const : ∀ x,
        rightExponent (rawCompact u) x =
          rightExponent (rawCompact u) (leftLength u) := by
      intro x
      rw [rightExponent, rightExponent, rawCompact_two, rawCompact_three,
        rawCompact_four, rawCompact_five]
      rw [hs]
      ring
    simp only [rightLength, if_pos hs]
    have hconstIntegral :
        (∫ x in leftLength u..leftLength u + (1 - u.p) / u.h,
          exp (rightExponent (rawCompact u) x)) =
            ∫ _x in leftLength u..leftLength u + (1 - u.p) / u.h, u.h := by
      apply intervalIntegral.integral_congr
      intro x _
      change exp (rightExponent (rawCompact u) x) = u.h
      rw [hexp_const x, hkinkR]
    rw [hconstIntegral]
    simp
    field_simp [ne_of_gt u.h_pos]
  · have hsActual :
        (rawCompact u) 3 - (rawCompact u) 4 = rightSlope u := by
      simp only [rawCompact_three, rawCompact_four]
      ring
    have hexp_affine : ∀ x,
        rightExponent (rawCompact u) x =
          (log u.l + (leftSlope u - rightSlope u) * leftLength u) +
            rightSlope u * x := by
      intro x
      simp only [rightExponent, rawCompact_two, rawCompact_three,
        rawCompact_four, rawCompact_five]
      ring
    have haffineIntegral :
        (∫ x in leftLength u..leftLength u + rightLength u,
          exp (rightExponent (rawCompact u) x)) =
            ∫ x in leftLength u..leftLength u + rightLength u,
              exp ((log u.l + (leftSlope u - rightSlope u) * leftLength u) +
                rightSlope u * x) := by
      apply intervalIntegral.integral_congr
      intro x _
      change exp (rightExponent (rawCompact u) x) = _
      rw [hexp_affine x]
    rw [haffineIntegral]
    have hend := rawCompact_rightEndpoint_value u
    rw [hexp_affine (leftLength u + rightLength u)] at hend
    have hstart := hkinkR
    rw [hexp_affine (leftLength u)] at hstart
    rw [integral_exp_affine_of_ne
      (log u.l + (leftSlope u - rightSlope u) * leftLength u)
      (rightSlope u) (leftLength u)
      (leftLength u + rightLength u) hs,
      hend, hstart]
    rw [div_eq_iff hs]
    simpa [mul_comm] using (rightSlope_mul_one_sub_p u).symm

theorem rawCompact_mass (u : InteriorProfile) :
    compactIntegral (fun _ : ℝ ↦ 1) (rawCompact u) = 1 := by
  unfold compactIntegral
  rw [rawCompact_left_mass, rawCompact_right_mass]
  ring

/-- Positivity of both raw subintervals follows from their strictly positive
masses; this avoids a separate case analysis of logarithm signs. -/
theorem leftLength_pos (u : InteriorProfile) : 0 < leftLength u := by
  by_contra h
  have hm : leftLength u ≤ 0 := le_of_not_gt h
  have hnonneg : 0 ≤
      (∫ x in leftLength u..0, exp (leftExponent (rawCompact u) x)) :=
    intervalIntegral.integral_nonneg_of_forall hm (fun x ↦ (exp_pos _).le)
  have hmass := rawCompact_left_mass u
  unfold leftIntegral leftIntegrand at hmass
  simp only [one_mul, rawCompact_zero, rawCompact_five] at hmass
  rw [intervalIntegral.integral_symm] at hmass
  linarith [u.p_pos]

theorem rightLength_pos (u : InteriorProfile) : 0 < rightLength u := by
  have hmass := rawCompact_right_mass u
  unfold rightIntegral rightIntegrand at hmass
  simp only [one_mul, rawCompact_five, rawCompact_one] at hmass
  by_contra h
  have hm : leftLength u + rightLength u ≤ leftLength u := by
    have : rightLength u ≤ 0 := le_of_not_gt h
    linarith
  have hnonneg : 0 ≤
      (∫ x in leftLength u + rightLength u..leftLength u,
        exp (rightExponent (rawCompact u) x)) :=
    intervalIntegral.integral_nonneg_of_forall hm (fun x ↦ (exp_pos _).le)
  rw [intervalIntegral.integral_symm] at hmass
  linarith [u.p_lt_one]

/-- The interior raw decoder really lands in the compact admissible chart. -/
theorem rawCompact_admissible (u : InteriorProfile) :
    (rawCompact u) 0 < (rawCompact u) 5 ∧
      (rawCompact u) 5 < (rawCompact u) 1 ∧
      0 ≤ (rawCompact u) 4 := by
  simp only [rawCompact_zero, rawCompact_one, rawCompact_four, rawCompact_five]
  exact ⟨leftLength_pos u,
    by linarith [rightLength_pos u],
    sub_nonneg.mpr (rightSlope_le_leftSlope u)⟩

/-! ## Centering and variance normalization of the interior decoder -/

def rawMean (u : InteriorProfile) : ℝ :=
  compactIntegral (fun x : ℝ ↦ x) (rawCompact u)

def rawSecondMoment (u : InteriorProfile) : ℝ :=
  compactIntegral (fun x : ℝ ↦ x ^ 2) (rawCompact u)

def rawVariance (u : InteriorProfile) : ℝ :=
  rawSecondMoment u - rawMean u ^ 2

/-- A nondegenerate admissible compact two-piece exponential has strictly
positive second moment. -/
lemma compactIntegral_sq_pos {p : CompactParam}
    (hp : p 0 < p 5 ∧ p 5 < p 1) :
    0 < compactIntegral (fun x : ℝ ↦ x ^ 2) p := by
  have hleft : 0 < leftIntegral (fun x : ℝ ↦ x ^ 2) p := by
    unfold leftIntegral leftIntegrand
    apply intervalIntegral.integral_pos hp.1
    · exact ((continuous_id.pow 2).mul (continuous_compactLeftWeight p)).continuousOn
    · intro x _
      exact mul_nonneg (sq_nonneg x) (exp_pos _).le
    · by_cases hA : p 0 = 0
      · refine ⟨p 5, ⟨hp.1.le, le_rfl⟩, ?_⟩
        rw [hA] at hp
        exact mul_pos (sq_pos_of_pos hp.1) (exp_pos _)
      · refine ⟨p 0, ⟨le_rfl, hp.1.le⟩, ?_⟩
        exact mul_pos (sq_pos_of_ne_zero hA) (exp_pos _)
  have hright : 0 ≤ rightIntegral (fun x : ℝ ↦ x ^ 2) p := by
    unfold rightIntegral rightIntegrand
    exact intervalIntegral.integral_nonneg_of_forall hp.2.le
      (fun x ↦ mul_nonneg (sq_nonneg x) (exp_pos _).le)
  unfold compactIntegral
  linarith

theorem rawVariance_pos (u : InteriorProfile) : 0 < rawVariance u := by
  let q := affineCompact (rawCompact u) (rawMean u) 1
  have hqadm := affineCompact_admissible (mu := rawMean u)
    (rawCompact_admissible u)
    (by norm_num : (0 : ℝ) < 1)
  have hpos : 0 < compactIntegral (fun x : ℝ ↦ x ^ 2) q :=
    compactIntegral_sq_pos ⟨hqadm.1, hqadm.2.1⟩
  have hformula := affineCompact_secondMoment (rawCompact u) (rawMean u) 1
    (by norm_num : (0 : ℝ) < 1)
  change compactIntegral (fun x : ℝ ↦ x ^ 2) q = _ at hformula
  rw [rawCompact_mass] at hformula
  simp only [div_one, one_pow, mul_one] at hformula
  unfold rawVariance rawSecondMoment rawMean
  unfold rawMean at hformula
  nlinarith

def rawSigma (u : InteriorProfile) : ℝ := sqrt (rawVariance u)

lemma rawSigma_pos (u : InteriorProfile) : 0 < rawSigma u := by
  exact Real.sqrt_pos.2 (rawVariance_pos u)

lemma rawSigma_sq (u : InteriorProfile) : rawSigma u ^ 2 = rawVariance u := by
  exact Real.sq_sqrt (rawVariance_pos u).le

/-- The centered, variance-one tagged compact decoder of a strictly interior
profile. -/
def decodeInterior (u : InteriorProfile) : LogConcaveFamily6.Param :=
  .compact (affineCompact (rawCompact u) (rawMean u) (rawSigma u))

theorem decodeInterior_mem_family6 (u : InteriorProfile) :
    decodeInterior u ∈ LogConcaveFamily6.family6 := by
  constructor
  · change
      (affineCompact (rawCompact u) (rawMean u) (rawSigma u)) 0 <
          (affineCompact (rawCompact u) (rawMean u) (rawSigma u)) 5 ∧
        (affineCompact (rawCompact u) (rawMean u) (rawSigma u)) 5 <
          (affineCompact (rawCompact u) (rawMean u) (rawSigma u)) 1 ∧
        0 ≤ (affineCompact (rawCompact u) (rawMean u) (rawSigma u)) 4
    exact affineCompact_admissible (rawCompact_admissible u) (rawSigma_pos u)
  · refine affineCompact_isIsotropic (rawCompact_mass u) rfl ?_
      (rawSigma_pos u)
    rw [rawSigma_sq]
    unfold rawVariance rawSecondMoment
    ring

/-- Affine normalization preserves the profile masses. -/
theorem decodeInterior_left_mass (u : InteriorProfile) :
    leftIntegral (fun _ : ℝ ↦ 1)
        (affineCompact (rawCompact u) (rawMean u) (rawSigma u)) = u.p := by
  rw [affineCompact_leftIntegral (fun _ : ℝ ↦ 1) (rawCompact u)
    (rawMean u) (rawSigma u) (rawSigma_pos u)]
  simpa using rawCompact_left_mass u

theorem decodeInterior_right_mass (u : InteriorProfile) :
    rightIntegral (fun _ : ℝ ↦ 1)
        (affineCompact (rawCompact u) (rawMean u) (rawSigma u)) = 1 - u.p := by
  rw [affineCompact_rightIntegral (fun _ : ℝ ↦ 1) (rawCompact u)
    (rawMean u) (rawSigma u) (rawSigma_pos u)]
  simpa using rawCompact_right_mass u

/-- The three density-profile heights acquire the common factor `rawSigma`
under standardization. -/
theorem decodeInterior_leftEndpoint_value (u : InteriorProfile) :
    exp (leftExponent
      (affineCompact (rawCompact u) (rawMean u) (rawSigma u))
      ((0 - rawMean u) / rawSigma u)) = rawSigma u * u.l := by
  rw [affineCompact_leftExponent (rawCompact u) (rawMean u) (rawSigma u)
    ((0 - rawMean u) / rawSigma u) (rawSigma_pos u)]
  have harg : rawSigma u * ((0 - rawMean u) / rawSigma u) + rawMean u = 0 := by
    field_simp [ne_of_gt (rawSigma_pos u)]
    ring
  rw [harg, rawCompact_leftEndpoint_value]

theorem decodeInterior_kink_value (u : InteriorProfile) :
    exp (leftExponent
      (affineCompact (rawCompact u) (rawMean u) (rawSigma u))
      ((leftLength u - rawMean u) / rawSigma u)) = rawSigma u * u.h := by
  rw [affineCompact_leftExponent (rawCompact u) (rawMean u) (rawSigma u)
    ((leftLength u - rawMean u) / rawSigma u) (rawSigma_pos u)]
  have harg : rawSigma u * ((leftLength u - rawMean u) / rawSigma u) +
      rawMean u = leftLength u := by
    field_simp [ne_of_gt (rawSigma_pos u)]
    ring
  rw [harg, rawCompact_kink_value]

theorem decodeInterior_rightEndpoint_value (u : InteriorProfile) :
    exp (rightExponent
      (affineCompact (rawCompact u) (rawMean u) (rawSigma u))
      ((leftLength u + rightLength u - rawMean u) / rawSigma u)) =
        rawSigma u * u.r := by
  rw [affineCompact_rightExponent (rawCompact u) (rawMean u) (rawSigma u)
    ((leftLength u + rightLength u - rawMean u) / rawSigma u)
    (rawSigma_pos u)]
  have harg : rawSigma u *
      ((leftLength u + rightLength u - rawMean u) / rawSigma u) +
        rawMean u = leftLength u + rightLength u := by
    field_simp [ne_of_gt (rawSigma_pos u)]
    ring
  rw [harg, rawCompact_rightEndpoint_value]

/-- Interior profile objective written in the raw coordinates. -/
def interiorObjective (alpha : ℝ) (u : InteriorProfile) : ℝ :=
  compactIntegral
    (fun x ↦ LogConcaveClaimI.gAlpha alpha
      ((x - rawMean u) / rawSigma u)) (rawCompact u)

theorem objective_decodeInterior (alpha : ℝ) (u : InteriorProfile) :
    LogConcaveFamily6.objective alpha (decodeInterior u) =
      interiorObjective alpha u := by
  exact affineCompact_integral (LogConcaveClaimI.gAlpha alpha) (rawCompact u)
    (rawMean u) (rawSigma u) (rawSigma_pos u)

/-! ## Profiles with zero endpoint height -/

/-- Profiles whose kink mass is strictly between zero and one, while either
endpoint height is allowed to vanish. -/
structure OpenKinkProfile where
  p : ℝ
  l : ℝ
  h : ℝ
  r : ℝ
  p_pos : 0 < p
  p_lt_one : p < 1
  l_nonneg : 0 ≤ l
  h_pos : 0 < h
  r_nonneg : 0 ≤ r
  concave : (1 - p) * l + p * r ≤ h

def openLeftSlope (u : OpenKinkProfile) : ℝ := (u.h - u.l) / u.p

def openRightSlope (u : OpenKinkProfile) : ℝ :=
  (u.r - u.h) / (1 - u.p)

def openLeftLength (u : OpenKinkProfile) : ℝ :=
  if openLeftSlope u = 0 then u.p / u.l
  else log (u.h / u.l) / openLeftSlope u

def openRightLength (u : OpenKinkProfile) : ℝ :=
  if openRightSlope u = 0 then (1 - u.p) / u.h
  else log (u.r / u.h) / openRightSlope u

lemma openRightSlope_le_leftSlope (u : OpenKinkProfile) :
    openRightSlope u ≤ openLeftSlope u := by
  rw [openRightSlope, openLeftSlope]
  apply (div_le_div_iff₀ (sub_pos.mpr u.p_lt_one) u.p_pos).2
  nlinarith [u.concave]

lemma openLeftSlope_mul_p (u : OpenKinkProfile) :
    openLeftSlope u * u.p = u.h - u.l := by
  rw [openLeftSlope]
  field_simp [ne_of_gt u.p_pos]

lemma openRightSlope_mul_one_sub_p (u : OpenKinkProfile) :
    openRightSlope u * (1 - u.p) = u.r - u.h := by
  rw [openRightSlope]
  field_simp [ne_of_gt (sub_pos.mpr u.p_lt_one)]

lemma integral_exp_affine_Iic (c s m : ℝ) (hs : 0 < s) :
    (∫ x : ℝ in Iic m, exp (c + s * x)) = exp (c + s * m) / s := by
  calc
    (∫ x : ℝ in Iic m, exp (c + s * x)) =
        ∫ x : ℝ in Iic m, exp c * exp (s * x) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      intro x _
      change exp (c + s * x) = exp c * exp (s * x)
      rw [exp_add]
    _ = exp c * (∫ x : ℝ in Iic m, exp (s * x)) :=
      MeasureTheory.integral_const_mul _ _
    _ = exp c * (exp (s * m) / s) := by rw [integral_exp_mul_Iic hs]
    _ = exp (c + s * m) / s := by rw [exp_add]; ring

lemma integral_exp_affine_Ioi (c s m : ℝ) (hs : s < 0) :
    (∫ x : ℝ in Ioi m, exp (c + s * x)) = -exp (c + s * m) / s := by
  calc
    (∫ x : ℝ in Ioi m, exp (c + s * x)) =
        ∫ x : ℝ in Ioi m, exp c * exp (s * x) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x _
      change exp (c + s * x) = exp c * exp (s * x)
      rw [exp_add]
    _ = exp c * (∫ x : ℝ in Ioi m, exp (s * x)) :=
      MeasureTheory.integral_const_mul _ _
    _ = exp c * (-exp (s * m) / s) := by rw [integral_exp_mul_Ioi hs]
    _ = -exp (c + s * m) / s := by rw [exp_add]; ring

/-! ### Vanishing left endpoint: finite-right support -/

/-- Raw parameter when `l=0<r`; the kink is placed at zero. -/
def rawFiniteRight (u : OpenKinkProfile) : HalfLineParam :=
  ![openRightLength u, log u.h, openLeftSlope u,
    openLeftSlope u - openRightSlope u, 0]

@[simp] lemma rawFiniteRight_zero (u : OpenKinkProfile) :
    rawFiniteRight u 0 = openRightLength u := rfl
@[simp] lemma rawFiniteRight_one (u : OpenKinkProfile) :
    rawFiniteRight u 1 = log u.h := rfl
@[simp] lemma rawFiniteRight_two (u : OpenKinkProfile) :
    rawFiniteRight u 2 = openLeftSlope u := rfl
@[simp] lemma rawFiniteRight_three (u : OpenKinkProfile) :
    rawFiniteRight u 3 = openLeftSlope u - openRightSlope u := rfl
@[simp] lemma rawFiniteRight_four (u : OpenKinkProfile) :
    rawFiniteRight u 4 = 0 := rfl

lemma openLeftSlope_pos_of_l_zero (u : OpenKinkProfile) (hl : u.l = 0) :
    0 < openLeftSlope u := by
  rw [openLeftSlope, hl]
  exact div_pos (by simpa using u.h_pos) u.p_pos

lemma rawFiniteRight_kink_value (u : OpenKinkProfile) :
    exp (finiteRightLeftExponent (rawFiniteRight u) 0) = u.h := by
  simp [finiteRightLeftExponent, Real.exp_log u.h_pos]

lemma rawFiniteRight_left_mass (u : OpenKinkProfile) (hl : u.l = 0) :
    finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) (rawFiniteRight u) = u.p := by
  unfold finiteRightLeftTailIntegral finiteRightLeftIntegrand
  simp only [one_mul, rawFiniteRight_four]
  change (∫ x : ℝ in Iic 0, exp (log u.h + openLeftSlope u * x)) = u.p
  rw [integral_exp_affine_Iic _ _ _ (openLeftSlope_pos_of_l_zero u hl)]
  simp only [mul_zero, add_zero, Real.exp_log u.h_pos]
  rw [div_eq_iff (openLeftSlope_pos_of_l_zero u hl).ne']
  have hs := openLeftSlope_mul_p u
  rw [hl, sub_zero] at hs
  simpa [mul_comm] using hs.symm

lemma rawFiniteRight_kink_right_value (u : OpenKinkProfile) :
    exp (finiteRightRightExponent (rawFiniteRight u) 0) = u.h := by
  simp [finiteRightRightExponent, Real.exp_log u.h_pos]

lemma rawFiniteRight_endpoint_value (u : OpenKinkProfile) (hr : 0 < u.r) :
    exp (finiteRightRightExponent (rawFiniteRight u) (openRightLength u)) = u.r := by
  simp only [finiteRightRightExponent, rawFiniteRight_one, rawFiniteRight_two,
    rawFiniteRight_three, rawFiniteRight_four, sub_zero]
  have hexp : log u.h + openRightSlope u * openRightLength u = log u.r := by
    unfold openRightLength
    split_ifs with hs
    · have hrh : u.r = u.h := by
        have h := openRightSlope_mul_one_sub_p u
        rw [hs, zero_mul] at h
        linarith
      rw [hrh, hs]
      ring
    · field_simp [hs]
      rw [Real.log_div hr.ne' u.h_pos.ne']
      ring
  rw [show log u.h + openLeftSlope u * openRightLength u -
      (openLeftSlope u - openRightSlope u) * openRightLength u =
        log u.h + openRightSlope u * openRightLength u by ring,
    hexp, Real.exp_log hr]

lemma rawFiniteRight_right_mass (u : OpenKinkProfile) (hr : 0 < u.r) :
    finiteRightRightCompactIntegral (fun _ : ℝ ↦ 1) (rawFiniteRight u) =
      1 - u.p := by
  unfold finiteRightRightCompactIntegral finiteRightRightIntegrand
  simp only [one_mul, rawFiniteRight_four, rawFiniteRight_zero]
  have hexp_affine : ∀ x,
      finiteRightRightExponent (rawFiniteRight u) x =
        log u.h + openRightSlope u * x := by
    intro x
    simp only [finiteRightRightExponent, rawFiniteRight_one,
      rawFiniteRight_two, rawFiniteRight_three, rawFiniteRight_four, sub_zero]
    ring
  have haffineIntegral :
      (∫ x in 0..openRightLength u,
        exp (finiteRightRightExponent (rawFiniteRight u) x)) =
          ∫ x in 0..openRightLength u,
            exp (log u.h + openRightSlope u * x) := by
    apply intervalIntegral.integral_congr
    intro x _
    change exp (finiteRightRightExponent (rawFiniteRight u) x) = _
    rw [hexp_affine x]
  rw [haffineIntegral]
  by_cases hs : openRightSlope u = 0
  · have hrh : u.r = u.h := by
      have h := openRightSlope_mul_one_sub_p u
      rw [hs, zero_mul] at h
      linarith
    simp [openRightLength, hs, Real.exp_log u.h_pos]
    field_simp [ne_of_gt u.h_pos]
  · rw [integral_exp_affine_of_ne (log u.h) (openRightSlope u) 0
      (openRightLength u) hs]
    have hend := rawFiniteRight_endpoint_value u hr
    rw [hexp_affine (openRightLength u)] at hend
    simp only [mul_zero, add_zero, Real.exp_log u.h_pos]
    rw [hend, div_eq_iff hs]
    simpa [mul_comm] using (openRightSlope_mul_one_sub_p u).symm

lemma openRightLength_pos_of_r_pos (u : OpenKinkProfile) (hr : 0 < u.r) :
    0 < openRightLength u := by
  have hmass := rawFiniteRight_right_mass u hr
  unfold finiteRightRightCompactIntegral finiteRightRightIntegrand at hmass
  simp only [one_mul, rawFiniteRight_four, rawFiniteRight_zero] at hmass
  by_contra h
  have hm : openRightLength u ≤ 0 := le_of_not_gt h
  have hnonneg : 0 ≤
      (∫ x in openRightLength u..0,
        exp (finiteRightRightExponent (rawFiniteRight u) x)) :=
    intervalIntegral.integral_nonneg_of_forall hm (fun x ↦ (exp_pos _).le)
  rw [intervalIntegral.integral_symm] at hmass
  linarith [u.p_lt_one]

theorem rawFiniteRight_admissible (u : OpenKinkProfile)
    (hl : u.l = 0) (hr : 0 < u.r) :
    LogConcaveFamily6.Admissible (.finiteRight (rawFiniteRight u)) := by
  change (rawFiniteRight u) 4 < (rawFiniteRight u) 0 ∧
    0 ≤ (rawFiniteRight u) 3 ∧ 0 < (rawFiniteRight u) 2
  simp only [rawFiniteRight_zero, rawFiniteRight_two, rawFiniteRight_three,
    rawFiniteRight_four]
  exact ⟨openRightLength_pos_of_r_pos u hr,
    sub_nonneg.mpr (openRightSlope_le_leftSlope u),
    openLeftSlope_pos_of_l_zero u hl⟩

theorem rawFiniteRight_mass (u : OpenKinkProfile)
    (hl : u.l = 0) (hr : 0 < u.r) :
    LogConcaveFamily6.integral (fun _ : ℝ ↦ 1)
      (.finiteRight (rawFiniteRight u)) = 1 := by
  change finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) (rawFiniteRight u) +
      finiteRightRightCompactIntegral (fun _ : ℝ ↦ 1) (rawFiniteRight u) = 1
  rw [rawFiniteRight_left_mass u hl, rawFiniteRight_right_mass u hr]
  ring

/-! ### Vanishing right endpoint: finite-left support -/

/-- Raw parameter when `0<l` and `r=0`; the finite left endpoint is placed
at zero. -/
def rawFiniteLeft (u : OpenKinkProfile) : HalfLineParam :=
  ![0, log u.l, openLeftSlope u,
    openLeftSlope u - openRightSlope u, openLeftLength u]

@[simp] lemma rawFiniteLeft_zero (u : OpenKinkProfile) :
    rawFiniteLeft u 0 = 0 := rfl
@[simp] lemma rawFiniteLeft_one (u : OpenKinkProfile) :
    rawFiniteLeft u 1 = log u.l := rfl
@[simp] lemma rawFiniteLeft_two (u : OpenKinkProfile) :
    rawFiniteLeft u 2 = openLeftSlope u := rfl
@[simp] lemma rawFiniteLeft_three (u : OpenKinkProfile) :
    rawFiniteLeft u 3 = openLeftSlope u - openRightSlope u := rfl
@[simp] lemma rawFiniteLeft_four (u : OpenKinkProfile) :
    rawFiniteLeft u 4 = openLeftLength u := rfl

lemma rawFiniteLeft_leftEndpoint_value (u : OpenKinkProfile) (hl : 0 < u.l) :
    exp (halfLineLeftExponent (rawFiniteLeft u) 0) = u.l := by
  simp [halfLineLeftExponent, Real.exp_log hl]

lemma rawFiniteLeft_kink_value (u : OpenKinkProfile) (hl : 0 < u.l) :
    exp (halfLineLeftExponent (rawFiniteLeft u) (openLeftLength u)) = u.h := by
  simp only [halfLineLeftExponent, rawFiniteLeft_one, rawFiniteLeft_two]
  unfold openLeftLength
  split_ifs with hs
  · have hhl : u.h = u.l := by
      have h := openLeftSlope_mul_p u
      rw [hs, zero_mul] at h
      linarith
    rw [hhl, hs]
    simp [Real.exp_log hl]
  · have heq : log u.l + openLeftSlope u *
        (log (u.h / u.l) / openLeftSlope u) = log u.h := by
      field_simp [hs]
      rw [Real.log_div u.h_pos.ne' hl.ne']
      ring
    rw [heq, Real.exp_log u.h_pos]

lemma rawFiniteLeft_left_mass (u : OpenKinkProfile) (hl : 0 < u.l) :
    halfLineLeftIntegral (fun _ : ℝ ↦ 1) (rawFiniteLeft u) = u.p := by
  unfold halfLineLeftIntegral halfLineLeftIntegrand
  simp only [one_mul, rawFiniteLeft_zero, rawFiniteLeft_four]
  change (∫ x in 0..openLeftLength u,
    exp (log u.l + openLeftSlope u * x)) = u.p
  by_cases hs : openLeftSlope u = 0
  · simp [openLeftLength, hs, Real.exp_log hl]
    field_simp [hl.ne']
  · rw [integral_exp_affine_of_ne (log u.l) (openLeftSlope u) 0
      (openLeftLength u) hs]
    have hk := rawFiniteLeft_kink_value u hl
    simp only [halfLineLeftExponent, rawFiniteLeft_one,
      rawFiniteLeft_two] at hk
    simp only [mul_zero, add_zero, Real.exp_log hl]
    rw [hk, div_eq_iff hs]
    simpa [mul_comm] using (openLeftSlope_mul_p u).symm

lemma openLeftLength_pos_of_l_pos (u : OpenKinkProfile) (hl : 0 < u.l) :
    0 < openLeftLength u := by
  have hmass := rawFiniteLeft_left_mass u hl
  unfold halfLineLeftIntegral halfLineLeftIntegrand at hmass
  simp only [one_mul, rawFiniteLeft_zero, rawFiniteLeft_four] at hmass
  by_contra h
  have hm : openLeftLength u ≤ 0 := le_of_not_gt h
  have hnonneg : 0 ≤
      (∫ x in openLeftLength u..0,
        exp (halfLineLeftExponent (rawFiniteLeft u) x)) :=
    intervalIntegral.integral_nonneg_of_forall hm (fun x ↦ (exp_pos _).le)
  rw [intervalIntegral.integral_symm] at hmass
  linarith [u.p_pos]

lemma openRightSlope_neg_of_r_zero (u : OpenKinkProfile) (hr : u.r = 0) :
    openRightSlope u < 0 := by
  rw [openRightSlope, hr]
  exact div_neg_of_neg_of_pos (by simpa using (neg_neg_of_pos u.h_pos))
    (sub_pos.mpr u.p_lt_one)

lemma rawFiniteLeft_kink_right_value (u : OpenKinkProfile) (hl : 0 < u.l) :
    exp (halfLineRightExponent (rawFiniteLeft u) (openLeftLength u)) = u.h := by
  rw [halfLineRightExponent, rawFiniteLeft_one, rawFiniteLeft_two,
    rawFiniteLeft_three, rawFiniteLeft_four, sub_self, mul_zero, sub_zero]
  exact rawFiniteLeft_kink_value u hl

lemma rawFiniteLeft_right_mass (u : OpenKinkProfile)
    (hl : 0 < u.l) (hr : u.r = 0) :
    halfLineRightIntegral (fun _ : ℝ ↦ 1) (rawFiniteLeft u) = 1 - u.p := by
  unfold halfLineRightIntegral halfLineRightIntegrand
  simp only [one_mul, rawFiniteLeft_four]
  have hexp_affine : ∀ x,
      halfLineRightExponent (rawFiniteLeft u) x =
        (log u.l + (openLeftSlope u - openRightSlope u) * openLeftLength u) +
          openRightSlope u * x := by
    intro x
    simp only [halfLineRightExponent, rawFiniteLeft_one, rawFiniteLeft_two,
      rawFiniteLeft_three, rawFiniteLeft_four]
    ring
  have haffineIntegral :
      (∫ x : ℝ in Ioi (openLeftLength u),
        exp (halfLineRightExponent (rawFiniteLeft u) x)) =
          ∫ x : ℝ in Ioi (openLeftLength u),
            exp ((log u.l + (openLeftSlope u - openRightSlope u) *
              openLeftLength u) + openRightSlope u * x) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    change exp (halfLineRightExponent (rawFiniteLeft u) x) = _
    rw [hexp_affine x]
  rw [haffineIntegral, integral_exp_affine_Ioi _ _ _
    (openRightSlope_neg_of_r_zero u hr)]
  have hk := rawFiniteLeft_kink_right_value u hl
  rw [hexp_affine (openLeftLength u)] at hk
  rw [hk]
  rw [div_eq_iff (openRightSlope_neg_of_r_zero u hr).ne]
  have hs := openRightSlope_mul_one_sub_p u
  rw [hr, zero_sub] at hs
  nlinarith

theorem rawFiniteLeft_admissible (u : OpenKinkProfile)
    (hl : 0 < u.l) (hr : u.r = 0) :
    LogConcaveFamily6.Admissible (.finiteLeft (rawFiniteLeft u)) := by
  change (rawFiniteLeft u) 0 < (rawFiniteLeft u) 4 ∧
    0 ≤ (rawFiniteLeft u) 3 ∧
      (rawFiniteLeft u) 2 - (rawFiniteLeft u) 3 < 0
  simp only [rawFiniteLeft_zero, rawFiniteLeft_two, rawFiniteLeft_three,
    rawFiniteLeft_four]
  exact ⟨openLeftLength_pos_of_l_pos u hl,
    sub_nonneg.mpr (openRightSlope_le_leftSlope u), by
      convert openRightSlope_neg_of_r_zero u hr using 1 <;> ring⟩

theorem rawFiniteLeft_mass (u : OpenKinkProfile)
    (hl : 0 < u.l) (hr : u.r = 0) :
    LogConcaveFamily6.integral (fun _ : ℝ ↦ 1)
      (.finiteLeft (rawFiniteLeft u)) = 1 := by
  change halfLineLeftIntegral (fun _ : ℝ ↦ 1) (rawFiniteLeft u) +
      halfLineRightIntegral (fun _ : ℝ ↦ 1) (rawFiniteLeft u) = 1
  rw [rawFiniteLeft_left_mass u hl, rawFiniteLeft_right_mass u hl hr]
  ring

/-! ### Both endpoint heights vanish: whole-line support -/

def rawWholeLine (u : OpenKinkProfile) : LogConcaveFamily6.WholeLineParam where
  c := log u.h
  beta := openLeftSlope u
  delta := openLeftSlope u - openRightSlope u
  m := 0

lemma rawWholeLine_admissible (u : OpenKinkProfile)
    (hl : u.l = 0) (hr : u.r = 0) :
    LogConcaveFamily6.Admissible (.wholeLine (rawWholeLine u)) := by
  change 0 ≤ (rawWholeLine u).delta ∧ 0 < (rawWholeLine u).beta ∧
    (rawWholeLine u).beta - (rawWholeLine u).delta < 0
  dsimp [rawWholeLine]
  exact ⟨sub_nonneg.mpr (openRightSlope_le_leftSlope u),
    openLeftSlope_pos_of_l_zero u hl, by
      convert openRightSlope_neg_of_r_zero u hr using 1 <;> ring⟩

lemma rawWholeLine_left_mass (u : OpenKinkProfile) (hl : u.l = 0) :
    (∫ x : ℝ in Iic 0, exp ((rawWholeLine u).c +
      (rawWholeLine u).beta * x)) = u.p := by
  dsimp [rawWholeLine]
  rw [integral_exp_affine_Iic _ _ _ (openLeftSlope_pos_of_l_zero u hl)]
  simp only [mul_zero, add_zero, Real.exp_log u.h_pos]
  rw [div_eq_iff (openLeftSlope_pos_of_l_zero u hl).ne']
  have hs := openLeftSlope_mul_p u
  rw [hl, sub_zero] at hs
  simpa [mul_comm] using hs.symm

lemma rawWholeLine_right_mass (u : OpenKinkProfile) (hr : u.r = 0) :
    (∫ x : ℝ in Ioi 0, exp ((rawWholeLine u).c +
      (rawWholeLine u).beta * x - (rawWholeLine u).delta * (x - 0))) =
        1 - u.p := by
  have hslope : ∀ x,
      (rawWholeLine u).c + (rawWholeLine u).beta * x -
          (rawWholeLine u).delta * (x - 0) =
        log u.h + openRightSlope u * x := by
    intro x
    dsimp [rawWholeLine]
    ring
  have haffine :
      (∫ x : ℝ in Ioi 0, exp ((rawWholeLine u).c +
        (rawWholeLine u).beta * x - (rawWholeLine u).delta * (x - 0))) =
          ∫ x : ℝ in Ioi 0, exp (log u.h + openRightSlope u * x) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    change exp ((rawWholeLine u).c + (rawWholeLine u).beta * x -
      (rawWholeLine u).delta * (x - 0)) =
        exp (log u.h + openRightSlope u * x)
    rw [hslope x]
  rw [haffine, integral_exp_affine_Ioi _ _ _
    (openRightSlope_neg_of_r_zero u hr)]
  simp only [mul_zero, add_zero, Real.exp_log u.h_pos]
  rw [div_eq_iff (openRightSlope_neg_of_r_zero u hr).ne]
  have hs := openRightSlope_mul_one_sub_p u
  rw [hr, zero_sub] at hs
  nlinarith

theorem rawWholeLine_mass (u : OpenKinkProfile)
    (hl : u.l = 0) (hr : u.r = 0) :
    LogConcaveFamily6.integral (fun _ : ℝ ↦ 1)
      (.wholeLine (rawWholeLine u)) = 1 := by
  simp only [LogConcaveFamily6.integral, one_mul]
  change (∫ x : ℝ in Iic 0, exp ((rawWholeLine u).c +
      (rawWholeLine u).beta * x)) +
    (∫ x : ℝ in Ioi 0, exp ((rawWholeLine u).c +
      (rawWholeLine u).beta * x - (rawWholeLine u).delta * (x - 0))) = 1
  rw [rawWholeLine_left_mass u hl, rawWholeLine_right_mass u hr]
  ring

/-! ## Affine normalization on unbounded support charts -/

/-- Positive affine change of variables on a right ray, in the precise form
needed for standardizing a density. -/
lemma integral_Ioi_standardize (F : ℝ → ℝ) (m mu sigma : ℝ)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ in Ioi ((m - mu) / sigma),
      sigma * F (sigma * y + mu)) = ∫ x : ℝ in Ioi m, F x := by
  let H : ℝ → ℝ := Set.indicator (Ioi m) F
  have hmap := MeasureTheory.integral_comp_mul_left_Ioi
    (fun z : ℝ ↦ F (m + z)) 0 hsigma
  simp only [mul_zero, inv_smul_smul₀ hsigma.ne', smul_eq_mul] at hmap
  have htranslate :
      (∫ z : ℝ in Ioi 0, F (m + z)) = ∫ x : ℝ in Ioi m, F x := by
    calc
      (∫ z : ℝ in Ioi 0, F (m + z)) =
          ∫ z : ℝ, H (z + m) := by
        rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with z
        by_cases hz : z ∈ Ioi (0 : ℝ)
        · have hzm : z + m ∈ Ioi m := by simpa [mem_Ioi] using add_lt_add_right hz m
          rw [indicator_of_mem hz, show H (z + m) = F (z + m) by
            exact indicator_of_mem hzm _]
          congr 1
          ring
        · have hzm : z + m ∉ Ioi m := by
            simp only [mem_Ioi, not_lt] at hz ⊢
            linarith
          simp [H, hz, hzm]
      _ = ∫ x : ℝ, H x := MeasureTheory.integral_add_right_eq_self H m
      _ = ∫ x : ℝ in Ioi m, F x :=
        MeasureTheory.integral_indicator measurableSet_Ioi
  calc
    (∫ y : ℝ in Ioi ((m - mu) / sigma),
        sigma * F (sigma * y + mu)) =
      ∫ z : ℝ in Ioi 0,
        sigma * F (sigma * (((m - mu) / sigma) + z) + mu) := by
      let G := fun y : ℝ ↦ sigma * F (sigma * y + mu)
      let K : ℝ → ℝ := Set.indicator (Ioi ((m - mu) / sigma)) G
      calc
        (∫ y : ℝ in Ioi ((m - mu) / sigma), G y) = ∫ y : ℝ, K y := by
          exact (MeasureTheory.integral_indicator measurableSet_Ioi).symm
        _ = ∫ z : ℝ, K (z + (m - mu) / sigma) := by
          rw [MeasureTheory.integral_add_right_eq_self]
        _ = ∫ z : ℝ in Ioi 0,
            G ((m - mu) / sigma + z) := by
          rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with z
          by_cases hz : z ∈ Ioi (0 : ℝ)
          · have hzK : z + (m - mu) / sigma ∈ Ioi ((m - mu) / sigma) := by
              simpa [mem_Ioi] using add_lt_add_right hz ((m - mu) / sigma)
            simp [K, G, hz, hzK, add_comm]
          · have hzK : z + (m - mu) / sigma ∉ Ioi ((m - mu) / sigma) := by
              simp only [mem_Ioi, not_lt] at hz ⊢
              linarith
            simp [K, G, hz, hzK]
        _ = _ := by rfl
    _ = sigma * (∫ z : ℝ in Ioi 0, F (m + sigma * z)) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro z _
      have hm : sigma * ((m - mu) / sigma + z) + mu = m + sigma * z := by
        field_simp [hsigma.ne']
        ring
      change sigma * F (sigma * ((m - mu) / sigma + z) + mu) =
        sigma * F (m + sigma * z)
      rw [hm]
    _ = ∫ z : ℝ in Ioi 0, F (m + z) := by
      rw [hmap]
      field_simp [hsigma.ne']
    _ = ∫ x : ℝ in Ioi m, F x := htranslate

/-- The corresponding positive affine change of variables on a left ray. -/
lemma integral_Iic_standardize (F : ℝ → ℝ) (m mu sigma : ℝ)
    (hsigma : 0 < sigma) :
    (∫ y : ℝ in Iic ((m - mu) / sigma),
      sigma * F (sigma * y + mu)) = ∫ x : ℝ in Iic m, F x := by
  have hleft :
      (∫ y : ℝ in Iic ((m - mu) / sigma),
        sigma * F (sigma * y + mu)) =
        ∫ z : ℝ in Ioi (-((m - mu) / sigma)),
          sigma * F (-sigma * z + mu) := by
    have h := integral_comp_neg_Iic ((m - mu) / sigma)
      (fun z : ℝ ↦ sigma * F (-sigma * z + mu))
    convert h using 1
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro x _
    congr 2
    ring_nf
  have hright :
      (∫ x : ℝ in Iic m, F x) = ∫ z : ℝ in Ioi (-m), F (-z) := by
    simpa only [neg_neg] using
      (integral_comp_neg_Iic m (fun z : ℝ ↦ F (-z)))
  rw [hleft, hright]
  have hchange := integral_Ioi_standardize (fun z : ℝ ↦ F (-z))
    (-m) (-mu) sigma hsigma
  convert hchange using 1 <;> ring_nf

/-- Parameters of `(X-mu)/sigma` in either half-line chart. -/
def affineHalfLine (p : HalfLineParam) (mu sigma : ℝ) : HalfLineParam :=
  ![(p 0 - mu) / sigma,
    log sigma + p 1 + p 2 * mu,
    p 2 * sigma,
    p 3 * sigma,
    (p 4 - mu) / sigma]

@[simp] lemma affineHalfLine_zero (p : HalfLineParam) (mu sigma : ℝ) :
    affineHalfLine p mu sigma 0 = (p 0 - mu) / sigma := rfl
@[simp] lemma affineHalfLine_one (p : HalfLineParam) (mu sigma : ℝ) :
    affineHalfLine p mu sigma 1 = log sigma + p 1 + p 2 * mu := rfl
@[simp] lemma affineHalfLine_two (p : HalfLineParam) (mu sigma : ℝ) :
    affineHalfLine p mu sigma 2 = p 2 * sigma := rfl
@[simp] lemma affineHalfLine_three (p : HalfLineParam) (mu sigma : ℝ) :
    affineHalfLine p mu sigma 3 = p 3 * sigma := rfl
@[simp] lemma affineHalfLine_four (p : HalfLineParam) (mu sigma : ℝ) :
    affineHalfLine p mu sigma 4 = (p 4 - mu) / sigma := rfl

lemma affineHalfLine_leftExponent (p : HalfLineParam) (mu sigma y : ℝ)
    (hsigma : 0 < sigma) :
    exp (halfLineLeftExponent (affineHalfLine p mu sigma) y) =
      sigma * exp (halfLineLeftExponent p (sigma * y + mu)) := by
  simp only [halfLineLeftExponent, affineHalfLine_one, affineHalfLine_two]
  calc
    exp (log sigma + p 1 + p 2 * mu + p 2 * sigma * y) =
        exp (log sigma + (p 1 + p 2 * (sigma * y + mu))) := by congr 1 <;> ring
    _ = exp (log sigma) * exp (p 1 + p 2 * (sigma * y + mu)) := exp_add _ _
    _ = _ := by rw [exp_log hsigma]

lemma affineHalfLine_rightExponent (p : HalfLineParam) (mu sigma y : ℝ)
    (hsigma : 0 < sigma) :
    exp (halfLineRightExponent (affineHalfLine p mu sigma) y) =
      sigma * exp (halfLineRightExponent p (sigma * y + mu)) := by
  simp only [halfLineRightExponent, affineHalfLine_one, affineHalfLine_two,
    affineHalfLine_three, affineHalfLine_four]
  have heq :
      log sigma + p 1 + p 2 * mu + p 2 * sigma * y -
          p 3 * sigma * (y - (p 4 - mu) / sigma) =
        log sigma + (p 1 + p 2 * (sigma * y + mu) -
          p 3 * (sigma * y + mu - p 4)) := by
    field_simp [hsigma.ne']
    ring
  rw [heq, exp_add, exp_log hsigma]

lemma affineHalfLine_leftIntegral (q : ℝ → ℝ) (p : HalfLineParam)
    (mu sigma : ℝ) (hsigma : 0 < sigma) :
    halfLineLeftIntegral q (affineHalfLine p mu sigma) =
      halfLineLeftIntegral (fun x ↦ q ((x - mu) / sigma)) p := by
  unfold halfLineLeftIntegral halfLineLeftIntegrand
  simp only [affineHalfLine_zero, affineHalfLine_four]
  have hcv := intervalIntegral.mul_integral_comp_mul_add
    (f := fun x : ℝ ↦ q ((x - mu) / sigma) * exp (halfLineLeftExponent p x))
    (a := (p 0 - mu) / sigma) (b := (p 4 - mu) / sigma) sigma mu
  rw [show sigma * ((p 0 - mu) / sigma) + mu = p 0 by field_simp [hsigma.ne']; ring,
    show sigma * ((p 4 - mu) / sigma) + mu = p 4 by field_simp [hsigma.ne']; ring]
    at hcv
  rw [← hcv, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  change q y * exp (halfLineLeftExponent (affineHalfLine p mu sigma) y) =
    sigma * (q ((sigma * y + mu - mu) / sigma) *
      exp (halfLineLeftExponent p (sigma * y + mu)))
  rw [affineHalfLine_leftExponent p mu sigma y hsigma]
  have : (sigma * y + mu - mu) / sigma = y := by field_simp [hsigma.ne']; ring
  rw [this]
  ring

lemma affineHalfLine_rightIntegral (q : ℝ → ℝ) (p : HalfLineParam)
    (mu sigma : ℝ) (hsigma : 0 < sigma) :
    halfLineRightIntegral q (affineHalfLine p mu sigma) =
      halfLineRightIntegral (fun x ↦ q ((x - mu) / sigma)) p := by
  unfold halfLineRightIntegral halfLineRightIntegrand
  simp only [affineHalfLine_four]
  let F := fun x : ℝ ↦ q ((x - mu) / sigma) * exp (halfLineRightExponent p x)
  rw [show (∫ y : ℝ in Ioi ((p 4 - mu) / sigma),
      q y * exp (halfLineRightExponent (affineHalfLine p mu sigma) y)) =
        ∫ y : ℝ in Ioi ((p 4 - mu) / sigma),
          sigma * F (sigma * y + mu) by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y _
    change q y * exp (halfLineRightExponent (affineHalfLine p mu sigma) y) =
      sigma * (q ((sigma * y + mu - mu) / sigma) *
        exp (halfLineRightExponent p (sigma * y + mu)))
    rw [affineHalfLine_rightExponent p mu sigma y hsigma]
    have : (sigma * y + mu - mu) / sigma = y := by field_simp [hsigma.ne']; ring
    rw [this]
    ring]
  exact integral_Ioi_standardize F (p 4) mu sigma hsigma

theorem affineFiniteLeft_integral (q : ℝ → ℝ) (p : HalfLineParam)
    (mu sigma : ℝ) (hsigma : 0 < sigma) :
    LogConcaveFamily6.integral q (.finiteLeft (affineHalfLine p mu sigma)) =
      LogConcaveFamily6.integral (fun x ↦ q ((x - mu) / sigma)) (.finiteLeft p) := by
  change halfLineLeftIntegral q (affineHalfLine p mu sigma) +
      halfLineRightIntegral q (affineHalfLine p mu sigma) =
    halfLineLeftIntegral (fun x ↦ q ((x - mu) / sigma)) p +
      halfLineRightIntegral (fun x ↦ q ((x - mu) / sigma)) p
  rw [affineHalfLine_leftIntegral q p mu sigma hsigma,
    affineHalfLine_rightIntegral q p mu sigma hsigma]

lemma affineHalfLine_finiteRightLeftExponent
    (p : HalfLineParam) (mu sigma y : ℝ) (hsigma : 0 < sigma) :
    exp (finiteRightLeftExponent (affineHalfLine p mu sigma) y) =
      sigma * exp (finiteRightLeftExponent p (sigma * y + mu)) := by
  simpa only [finiteRightLeftExponent, halfLineLeftExponent] using
    affineHalfLine_leftExponent p mu sigma y hsigma

lemma affineHalfLine_finiteRightRightExponent
    (p : HalfLineParam) (mu sigma y : ℝ) (hsigma : 0 < sigma) :
    exp (finiteRightRightExponent (affineHalfLine p mu sigma) y) =
      sigma * exp (finiteRightRightExponent p (sigma * y + mu)) := by
  simpa only [finiteRightRightExponent, halfLineRightExponent] using
    affineHalfLine_rightExponent p mu sigma y hsigma

lemma affineFiniteRight_leftTailIntegral
    (q : ℝ → ℝ) (p : HalfLineParam) (mu sigma : ℝ)
    (hsigma : 0 < sigma) :
    finiteRightLeftTailIntegral q (affineHalfLine p mu sigma) =
      finiteRightLeftTailIntegral (fun x ↦ q ((x - mu) / sigma)) p := by
  unfold finiteRightLeftTailIntegral finiteRightLeftIntegrand
  simp only [affineHalfLine_four]
  let F := fun x : ℝ ↦ q ((x - mu) / sigma) * exp (finiteRightLeftExponent p x)
  have heq :
      (∫ y : ℝ in Iic ((p 4 - mu) / sigma),
        q y * exp (finiteRightLeftExponent (affineHalfLine p mu sigma) y)) =
          ∫ y : ℝ in Iic ((p 4 - mu) / sigma),
            sigma * F (sigma * y + mu) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro y _
    change q y * exp (finiteRightLeftExponent (affineHalfLine p mu sigma) y) =
      sigma * (q ((sigma * y + mu - mu) / sigma) *
        exp (finiteRightLeftExponent p (sigma * y + mu)))
    rw [affineHalfLine_finiteRightLeftExponent p mu sigma y hsigma]
    have : (sigma * y + mu - mu) / sigma = y := by field_simp [hsigma.ne']; ring
    rw [this]
    ring
  rw [heq]
  exact integral_Iic_standardize F (p 4) mu sigma hsigma

lemma affineFiniteRight_rightCompactIntegral
    (q : ℝ → ℝ) (p : HalfLineParam) (mu sigma : ℝ)
    (hsigma : 0 < sigma) :
    finiteRightRightCompactIntegral q (affineHalfLine p mu sigma) =
      finiteRightRightCompactIntegral (fun x ↦ q ((x - mu) / sigma)) p := by
  unfold finiteRightRightCompactIntegral finiteRightRightIntegrand
  simp only [affineHalfLine_four, affineHalfLine_zero]
  have hcv := intervalIntegral.mul_integral_comp_mul_add
    (f := fun x : ℝ ↦ q ((x - mu) / sigma) * exp (finiteRightRightExponent p x))
    (a := (p 4 - mu) / sigma) (b := (p 0 - mu) / sigma) sigma mu
  rw [show sigma * ((p 4 - mu) / sigma) + mu = p 4 by field_simp [hsigma.ne']; ring,
    show sigma * ((p 0 - mu) / sigma) + mu = p 0 by field_simp [hsigma.ne']; ring]
    at hcv
  rw [← hcv, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  change q y * exp (finiteRightRightExponent (affineHalfLine p mu sigma) y) =
    sigma * (q ((sigma * y + mu - mu) / sigma) *
      exp (finiteRightRightExponent p (sigma * y + mu)))
  rw [affineHalfLine_finiteRightRightExponent p mu sigma y hsigma]
  have : (sigma * y + mu - mu) / sigma = y := by field_simp [hsigma.ne']; ring
  rw [this]
  ring

theorem affineFiniteRight_integral (q : ℝ → ℝ) (p : HalfLineParam)
    (mu sigma : ℝ) (hsigma : 0 < sigma) :
    LogConcaveFamily6.integral q (.finiteRight (affineHalfLine p mu sigma)) =
      LogConcaveFamily6.integral (fun x ↦ q ((x - mu) / sigma)) (.finiteRight p) := by
  change finiteRightLeftTailIntegral q (affineHalfLine p mu sigma) +
      finiteRightRightCompactIntegral q (affineHalfLine p mu sigma) =
    finiteRightLeftTailIntegral (fun x ↦ q ((x - mu) / sigma)) p +
      finiteRightRightCompactIntegral (fun x ↦ q ((x - mu) / sigma)) p
  rw [affineFiniteRight_leftTailIntegral q p mu sigma hsigma,
    affineFiniteRight_rightCompactIntegral q p mu sigma hsigma]

/-- Parameters of `(X-mu)/sigma` in the whole-line chart. -/
def affineWholeLine (p : LogConcaveFamily6.WholeLineParam) (mu sigma : ℝ) :
    LogConcaveFamily6.WholeLineParam where
  c := log sigma + p.c + p.beta * mu
  beta := p.beta * sigma
  delta := p.delta * sigma
  m := (p.m - mu) / sigma

lemma affineWholeLine_leftExponent
    (p : LogConcaveFamily6.WholeLineParam) (mu sigma y : ℝ)
    (hsigma : 0 < sigma) :
    exp ((affineWholeLine p mu sigma).c +
      (affineWholeLine p mu sigma).beta * y) =
        sigma * exp (p.c + p.beta * (sigma * y + mu)) := by
  dsimp [affineWholeLine]
  calc
    exp (log sigma + p.c + p.beta * mu + p.beta * sigma * y) =
        exp (log sigma + (p.c + p.beta * (sigma * y + mu))) := by congr 1 <;> ring
    _ = exp (log sigma) * exp (p.c + p.beta * (sigma * y + mu)) := exp_add _ _
    _ = _ := by rw [exp_log hsigma]

lemma affineWholeLine_rightExponent
    (p : LogConcaveFamily6.WholeLineParam) (mu sigma y : ℝ)
    (hsigma : 0 < sigma) :
    exp ((affineWholeLine p mu sigma).c +
      (affineWholeLine p mu sigma).beta * y -
      (affineWholeLine p mu sigma).delta *
        (y - (affineWholeLine p mu sigma).m)) =
      sigma * exp (p.c + p.beta * (sigma * y + mu) -
        p.delta * (sigma * y + mu - p.m)) := by
  dsimp [affineWholeLine]
  have heq :
      log sigma + p.c + p.beta * mu + p.beta * sigma * y -
          p.delta * sigma * (y - (p.m - mu) / sigma) =
        log sigma + (p.c + p.beta * (sigma * y + mu) -
          p.delta * (sigma * y + mu - p.m)) := by
    field_simp [hsigma.ne']
    ring
  rw [heq, exp_add, exp_log hsigma]

theorem affineWholeLine_integral (q : ℝ → ℝ)
    (p : LogConcaveFamily6.WholeLineParam) (mu sigma : ℝ)
    (hsigma : 0 < sigma) :
    LogConcaveFamily6.integral q (.wholeLine (affineWholeLine p mu sigma)) =
      LogConcaveFamily6.integral (fun x ↦ q ((x - mu) / sigma)) (.wholeLine p) := by
  change
    (∫ y : ℝ in Iic ((p.m - mu) / sigma),
      q y * exp ((affineWholeLine p mu sigma).c +
        (affineWholeLine p mu sigma).beta * y)) +
    (∫ y : ℝ in Ioi ((p.m - mu) / sigma),
      q y * exp ((affineWholeLine p mu sigma).c +
        (affineWholeLine p mu sigma).beta * y -
        (affineWholeLine p mu sigma).delta *
          (y - (affineWholeLine p mu sigma).m))) = _
  let FL := fun x : ℝ ↦ q ((x - mu) / sigma) * exp (p.c + p.beta * x)
  let FR := fun x : ℝ ↦ q ((x - mu) / sigma) *
    exp (p.c + p.beta * x - p.delta * (x - p.m))
  have hL :
      (∫ y : ℝ in Iic ((p.m - mu) / sigma),
        q y * exp ((affineWholeLine p mu sigma).c +
          (affineWholeLine p mu sigma).beta * y)) =
        ∫ y : ℝ in Iic ((p.m - mu) / sigma),
          sigma * FL (sigma * y + mu) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro y _
    change q y * exp ((affineWholeLine p mu sigma).c +
      (affineWholeLine p mu sigma).beta * y) =
      sigma * (q ((sigma * y + mu - mu) / sigma) *
        exp (p.c + p.beta * (sigma * y + mu)))
    rw [affineWholeLine_leftExponent p mu sigma y hsigma]
    have : (sigma * y + mu - mu) / sigma = y := by field_simp [hsigma.ne']; ring
    rw [this]
    ring
  have hR :
      (∫ y : ℝ in Ioi ((p.m - mu) / sigma),
        q y * exp ((affineWholeLine p mu sigma).c +
          (affineWholeLine p mu sigma).beta * y -
          (affineWholeLine p mu sigma).delta *
            (y - (affineWholeLine p mu sigma).m))) =
        ∫ y : ℝ in Ioi ((p.m - mu) / sigma),
          sigma * FR (sigma * y + mu) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y _
    change q y * exp ((affineWholeLine p mu sigma).c +
      (affineWholeLine p mu sigma).beta * y -
      (affineWholeLine p mu sigma).delta *
        (y - (affineWholeLine p mu sigma).m)) =
      sigma * (q ((sigma * y + mu - mu) / sigma) *
        exp (p.c + p.beta * (sigma * y + mu) -
          p.delta * (sigma * y + mu - p.m)))
    rw [affineWholeLine_rightExponent p mu sigma y hsigma]
    have : (sigma * y + mu - mu) / sigma = y := by field_simp [hsigma.ne']; ring
    rw [this]
    ring
  rw [hL, hR, integral_Iic_standardize FL p.m mu sigma hsigma,
    integral_Ioi_standardize FR p.m mu sigma hsigma]
  rfl

/-- Uniform affine normalization on all four support tags. -/
def affineParam (p : LogConcaveFamily6.Param) (mu sigma : ℝ) :
    LogConcaveFamily6.Param :=
  match p with
  | .compact u => .compact (affineCompact u mu sigma)
  | .finiteLeft u => .finiteLeft (affineHalfLine u mu sigma)
  | .finiteRight u => .finiteRight (affineHalfLine u mu sigma)
  | .wholeLine u => .wholeLine (affineWholeLine u mu sigma)

theorem affineParam_integral (q : ℝ → ℝ) (p : LogConcaveFamily6.Param)
    (mu sigma : ℝ) (hsigma : 0 < sigma) :
    LogConcaveFamily6.integral q (affineParam p mu sigma) =
      LogConcaveFamily6.integral (fun x ↦ q ((x - mu) / sigma)) p := by
  cases p with
  | compact u => exact affineCompact_integral q u mu sigma hsigma
  | finiteLeft u => exact affineFiniteLeft_integral q u mu sigma hsigma
  | finiteRight u => exact affineFiniteRight_integral q u mu sigma hsigma
  | wholeLine u => exact affineWholeLine_integral q u mu sigma hsigma

theorem affineParam_admissible {p : LogConcaveFamily6.Param} {mu sigma : ℝ}
    (hp : LogConcaveFamily6.Admissible p) (hsigma : 0 < sigma) :
    LogConcaveFamily6.Admissible (affineParam p mu sigma) := by
  cases p with
  | compact u =>
      exact affineCompact_admissible hp hsigma
  | finiteLeft u =>
      change u 0 < u 4 ∧ 0 ≤ u 3 ∧ u 2 - u 3 < 0 at hp
      change (affineHalfLine u mu sigma) 0 < (affineHalfLine u mu sigma) 4 ∧
        0 ≤ (affineHalfLine u mu sigma) 3 ∧
          (affineHalfLine u mu sigma) 2 - (affineHalfLine u mu sigma) 3 < 0
      simp only [affineHalfLine_zero, affineHalfLine_two,
        affineHalfLine_three, affineHalfLine_four]
      exact ⟨(div_lt_div_iff_of_pos_right hsigma).2
          (sub_lt_sub_right hp.1 mu),
        mul_nonneg hp.2.1 hsigma.le, by
          nlinarith [mul_pos (neg_pos.mpr hp.2.2) hsigma]⟩
  | finiteRight u =>
      change u 4 < u 0 ∧ 0 ≤ u 3 ∧ 0 < u 2 at hp
      change (affineHalfLine u mu sigma) 4 < (affineHalfLine u mu sigma) 0 ∧
        0 ≤ (affineHalfLine u mu sigma) 3 ∧
          0 < (affineHalfLine u mu sigma) 2
      simp only [affineHalfLine_zero, affineHalfLine_two,
        affineHalfLine_three, affineHalfLine_four]
      exact ⟨(div_lt_div_iff_of_pos_right hsigma).2
          (sub_lt_sub_right hp.1 mu),
        mul_nonneg hp.2.1 hsigma.le, mul_pos hp.2.2 hsigma⟩
  | wholeLine u =>
      change 0 ≤ u.delta ∧ 0 < u.beta ∧ u.beta - u.delta < 0 at hp
      change 0 ≤ (affineWholeLine u mu sigma).delta ∧
        0 < (affineWholeLine u mu sigma).beta ∧
          (affineWholeLine u mu sigma).beta -
            (affineWholeLine u mu sigma).delta < 0
      dsimp [affineWholeLine]
      exact ⟨mul_nonneg hp.1 hsigma.le, mul_pos hp.2.1 hsigma, by
        nlinarith [mul_pos (neg_pos.mpr hp.2.2) hsigma]⟩

/-! ### Generic moment normalization -/

def paramMass (p : LogConcaveFamily6.Param) : ℝ :=
  LogConcaveFamily6.integral (fun _ : ℝ ↦ 1) p

def paramMean (p : LogConcaveFamily6.Param) : ℝ :=
  LogConcaveFamily6.integral (fun x : ℝ ↦ x) p

def paramSecondMoment (p : LogConcaveFamily6.Param) : ℝ :=
  LogConcaveFamily6.integral (fun x : ℝ ↦ x ^ 2) p

def paramVariance (p : LogConcaveFamily6.Param) : ℝ :=
  paramSecondMoment p - paramMean p ^ 2

lemma pieceIntegrable_linear {p : LogConcaveFamily6.Param}
    (a b : ℝ) (q r : ℝ → ℝ)
    (hq : LogConcaveFamily6.Law.PieceIntegrable p q)
    (hr : LogConcaveFamily6.Law.PieceIntegrable p r) :
    LogConcaveFamily6.Law.PieceIntegrable p (fun x ↦ a * q x + b * r x) := by
  cases p <;> change _ ∧ _ at hq hr ⊢
  all_goals constructor
  all_goals
    first
    | apply ((hq.1.const_mul a).add (hr.1.const_mul b)).congr
    | apply ((hq.2.const_mul a).add (hr.2.const_mul b)).congr
  all_goals
    filter_upwards [] with x
    dsimp
    ring

lemma paramIntegral_linear {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.Admissible p) (a b : ℝ)
    (q r : ℝ → ℝ) (hq : LogConcaveFamily6.Law.PieceIntegrable p q)
    (hr : LogConcaveFamily6.Law.PieceIntegrable p r) :
    LogConcaveFamily6.integral (fun x ↦ a * q x + b * r x) p =
      a * LogConcaveFamily6.integral q p +
        b * LogConcaveFamily6.integral r p := by
  open LogConcaveFamily6.Law in
    rw [← integral_rawMeasure_eq_tagged hp _
      (pieceIntegrable_linear a b q r hq hr),
      MeasureTheory.integral_add
        ((integrable_rawMeasure_of_piece hq).const_mul a)
        ((integrable_rawMeasure_of_piece hr).const_mul b),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      integral_rawMeasure_eq_tagged hp q hq,
      integral_rawMeasure_eq_tagged hp r hr]

lemma affineParam_mass (p : LogConcaveFamily6.Param) (mu sigma : ℝ)
    (hsigma : 0 < sigma) :
    paramMass (affineParam p mu sigma) = paramMass p := by
  unfold paramMass
  simpa using affineParam_integral (fun _ : ℝ ↦ 1) p mu sigma hsigma

lemma affineParam_firstMoment {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.Admissible p) (mu sigma : ℝ)
    (hsigma : 0 < sigma) :
    paramMean (affineParam p mu sigma) =
      (paramMean p - mu * paramMass p) / sigma := by
  unfold paramMean
  rw [affineParam_integral (fun x : ℝ ↦ x) p mu sigma hsigma]
  have hq := LogConcaveFamily6.Law.pieceIntegrable_pow 1 hp
  have hr := LogConcaveFamily6.Law.pieceIntegrable_one hp
  rw [show LogConcaveFamily6.integral (fun x ↦ (x - mu) / sigma) p =
      LogConcaveFamily6.integral
        (fun x ↦ sigma⁻¹ * x + (-mu * sigma⁻¹) * 1) p by
    apply congrArg (fun f : ℝ → ℝ ↦ LogConcaveFamily6.integral f p)
    funext x
    field_simp [hsigma.ne']
    ring,
    paramIntegral_linear hp sigma⁻¹ (-mu * sigma⁻¹)
      (fun x : ℝ ↦ x) (fun _ : ℝ ↦ 1) (by simpa using hq) hr]
  simp only [paramMean, paramMass]
  field_simp [hsigma.ne']
  ring

lemma affineParam_secondMoment {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.Admissible p) (mu sigma : ℝ)
    (hsigma : 0 < sigma) :
    paramSecondMoment (affineParam p mu sigma) =
      (paramSecondMoment p - 2 * mu * paramMean p + mu ^ 2 * paramMass p) /
        sigma ^ 2 := by
  unfold paramSecondMoment
  rw [affineParam_integral (fun x : ℝ ↦ x ^ 2) p mu sigma hsigma]
  have hs2 : sigma ^ 2 ≠ 0 := pow_ne_zero 2 hsigma.ne'
  have h2 := LogConcaveFamily6.Law.pieceIntegrable_pow 2 hp
  have h1 : LogConcaveFamily6.Law.PieceIntegrable p (fun x : ℝ ↦ x) := by
    simpa only [pow_one] using LogConcaveFamily6.Law.pieceIntegrable_pow 1 hp
  have h0 := LogConcaveFamily6.Law.pieceIntegrable_one hp
  have hfirst :
      LogConcaveFamily6.integral
        (fun x : ℝ ↦ (sigma ^ 2)⁻¹ * x ^ 2 +
          ((-2 * mu) * (sigma ^ 2)⁻¹) * x) p =
      (sigma ^ 2)⁻¹ * LogConcaveFamily6.integral (fun x : ℝ ↦ x ^ 2) p +
        ((-2 * mu) * (sigma ^ 2)⁻¹) *
          LogConcaveFamily6.integral (fun x : ℝ ↦ x) p := by
    exact paramIntegral_linear hp _ _ _ _ h2 h1
  rw [show LogConcaveFamily6.integral (fun x ↦ ((x - mu) / sigma) ^ 2) p =
      LogConcaveFamily6.integral
        (fun x ↦ 1 * ((sigma ^ 2)⁻¹ * x ^ 2 +
          ((-2 * mu) * (sigma ^ 2)⁻¹) * x) +
          (mu ^ 2 * (sigma ^ 2)⁻¹) * 1) p by
    apply congrArg (fun f : ℝ → ℝ ↦ LogConcaveFamily6.integral f p)
    funext x
    field_simp [hs2]
    ring,
    paramIntegral_linear hp 1 (mu ^ 2 * (sigma ^ 2)⁻¹)
      (fun x ↦ (sigma ^ 2)⁻¹ * x ^ 2 +
        ((-2 * mu) * (sigma ^ 2)⁻¹) * x)
      (fun _ : ℝ ↦ 1)
      (pieceIntegrable_linear _ _ _ _ h2 h1) h0,
    hfirst]
  simp only [paramSecondMoment, paramMean, paramMass]
  field_simp [hs2]
  ring

lemma interval_sq_mul_pos (a b : ℝ) (hab : a < b) (w : ℝ → ℝ)
    (hw : Continuous w) (hwpos : ∀ x, 0 < w x) :
    0 < ∫ x in a..b, x ^ 2 * w x := by
  apply intervalIntegral.integral_pos hab
  · exact ((continuous_id.pow 2).mul hw).continuousOn
  · intro x _
    exact mul_nonneg (sq_nonneg x) (hwpos x).le
  · by_cases ha : a = 0
    · refine ⟨b, ⟨hab.le, le_rfl⟩, ?_⟩
      rw [ha] at hab
      exact mul_pos (sq_pos_of_pos hab) (hwpos b)
    · exact ⟨a, ⟨le_rfl, hab.le⟩,
        mul_pos (sq_pos_of_ne_zero ha) (hwpos a)⟩

/-- Every admissible member of family (6) is nondegenerate, hence has
strictly positive second moment. -/
theorem paramSecondMoment_pos {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.Admissible p) : 0 < paramSecondMoment p := by
  cases p with
  | compact u =>
      change 0 < compactIntegral (fun x : ℝ ↦ x ^ 2) u
      exact compactIntegral_sq_pos ⟨hp.1, hp.2.1⟩
  | finiteLeft u =>
      change u 0 < u 4 ∧ 0 ≤ u 3 ∧ u 2 - u 3 < 0 at hp
      change 0 < halfLineLeftIntegral (fun x : ℝ ↦ x ^ 2) u +
        halfLineRightIntegral (fun x : ℝ ↦ x ^ 2) u
      have hleft : 0 < halfLineLeftIntegral (fun x : ℝ ↦ x ^ 2) u := by
        unfold halfLineLeftIntegral halfLineLeftIntegrand
        exact interval_sq_mul_pos _ _ hp.1 _
          (show Continuous (fun x : ℝ ↦ exp (halfLineLeftExponent u x)) by
            unfold halfLineLeftExponent; fun_prop)
          (fun x ↦ exp_pos _)
      have hright : 0 ≤ halfLineRightIntegral (fun x : ℝ ↦ x ^ 2) u := by
        unfold halfLineRightIntegral halfLineRightIntegrand
        exact MeasureTheory.integral_nonneg_of_ae
          (ae_of_all _ fun x ↦ mul_nonneg (sq_nonneg x) (exp_pos _).le)
      linarith
  | finiteRight u =>
      change u 4 < u 0 ∧ 0 ≤ u 3 ∧ 0 < u 2 at hp
      change 0 < finiteRightLeftTailIntegral (fun x : ℝ ↦ x ^ 2) u +
        finiteRightRightCompactIntegral (fun x : ℝ ↦ x ^ 2) u
      have hleft : 0 ≤ finiteRightLeftTailIntegral (fun x : ℝ ↦ x ^ 2) u := by
        unfold finiteRightLeftTailIntegral finiteRightLeftIntegrand
        exact MeasureTheory.integral_nonneg_of_ae
          (ae_of_all _ fun x ↦ mul_nonneg (sq_nonneg x) (exp_pos _).le)
      have hright : 0 < finiteRightRightCompactIntegral
          (fun x : ℝ ↦ x ^ 2) u := by
        unfold finiteRightRightCompactIntegral finiteRightRightIntegrand
        exact interval_sq_mul_pos _ _ hp.1 _
          (show Continuous (fun x : ℝ ↦ exp (finiteRightRightExponent u x)) by
            unfold finiteRightRightExponent; fun_prop)
          (fun x ↦ exp_pos _)
      linarith
  | wholeLine u =>
      change 0 ≤ u.delta ∧ 0 < u.beta ∧ u.beta - u.delta < 0 at hp
      change 0 <
        (∫ x : ℝ in Iic u.m, x ^ 2 * exp (u.c + u.beta * x)) +
        (∫ x : ℝ in Ioi u.m,
          x ^ 2 * exp (u.c + u.beta * x - u.delta * (x - u.m)))
      have hpiece := LogConcaveFamily6.Law.pieceIntegrable_sq
        (p := LogConcaveFamily6.Param.wholeLine u) hp
      have hsmall : 0 < ∫ x in u.m - 1..u.m,
          x ^ 2 * exp (u.c + u.beta * x) := by
        exact interval_sq_mul_pos _ _ (by linarith) _
          (show Continuous (fun x : ℝ ↦ exp (u.c + u.beta * x)) by fun_prop)
          (fun x ↦ exp_pos _)
      have hmono :
          (∫ x in u.m - 1..u.m, x ^ 2 * exp (u.c + u.beta * x)) ≤
            ∫ x : ℝ in Iic u.m, x ^ 2 * exp (u.c + u.beta * x) := by
        rw [intervalIntegral.integral_of_le (by linarith : u.m - 1 ≤ u.m)]
        exact MeasureTheory.setIntegral_mono_set hpiece.1
          (ae_of_all _ fun x ↦ mul_nonneg (sq_nonneg x) (exp_pos _).le)
          (Filter.Eventually.of_forall fun x hx ↦ by
            exact mem_Iic.mpr hx.2)
      have hleft : 0 < ∫ x : ℝ in Iic u.m,
          x ^ 2 * exp (u.c + u.beta * x) := lt_of_lt_of_le hsmall hmono
      have hright : 0 ≤ ∫ x : ℝ in Ioi u.m,
          x ^ 2 * exp (u.c + u.beta * x - u.delta * (x - u.m)) :=
        MeasureTheory.integral_nonneg_of_ae
          (ae_of_all _ fun x ↦ mul_nonneg (sq_nonneg x) (exp_pos _).le)
      linarith

theorem paramVariance_pos_of_mass_one {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.Admissible p) (hmass : paramMass p = 1) :
    0 < paramVariance p := by
  let q := affineParam p (paramMean p) 1
  have hqadm := affineParam_admissible (mu := paramMean p) hp
    (by norm_num : (0 : ℝ) < 1)
  have hpos := paramSecondMoment_pos hqadm
  have hformula := affineParam_secondMoment hp (paramMean p) 1
    (by norm_num : (0 : ℝ) < 1)
  change paramSecondMoment q = _ at hformula
  rw [hmass] at hformula
  simp only [div_one, one_pow, mul_one] at hformula
  unfold paramVariance
  nlinarith

def paramSigma (p : LogConcaveFamily6.Param) : ℝ := sqrt (paramVariance p)

lemma paramSigma_pos_of_mass_one {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.Admissible p) (hmass : paramMass p = 1) :
    0 < paramSigma p := Real.sqrt_pos.2 (paramVariance_pos_of_mass_one hp hmass)

lemma paramSigma_sq_of_mass_one {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.Admissible p) (hmass : paramMass p = 1) :
    paramSigma p ^ 2 = paramVariance p :=
  Real.sq_sqrt (paramVariance_pos_of_mass_one hp hmass).le

def normalizeParam (p : LogConcaveFamily6.Param) : LogConcaveFamily6.Param :=
  affineParam p (paramMean p) (paramSigma p)

theorem normalizeParam_mem_family6 {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.Admissible p) (hmass : paramMass p = 1) :
    normalizeParam p ∈ LogConcaveFamily6.family6 := by
  have hsigma := paramSigma_pos_of_mass_one hp hmass
  constructor
  · exact affineParam_admissible hp hsigma
  · funext k
    fin_cases k
    · change paramMass (normalizeParam p) = 1
      rw [normalizeParam, affineParam_mass p (paramMean p) (paramSigma p) hsigma,
        hmass]
    · simp only [LogConcaveFamily6.momentMap, LogConcaveFamily6.isotropicTarget,
        LogConcaveFamily6.integral, pow_one]
      change paramMean (normalizeParam p) = 0
      rw [normalizeParam, affineParam_firstMoment hp (paramMean p) (paramSigma p) hsigma,
        hmass]
      field_simp [hsigma.ne']
      ring
    · simp only [LogConcaveFamily6.momentMap, LogConcaveFamily6.isotropicTarget,
        LogConcaveFamily6.integral]
      change paramSecondMoment (normalizeParam p) = 1
      rw [normalizeParam, affineParam_secondMoment hp (paramMean p) (paramSigma p) hsigma,
        hmass, paramSigma_sq_of_mass_one hp hmass]
      unfold paramVariance
      have hvar : paramSecondMoment p - paramMean p ^ 2 ≠ 0 := by
        exact (paramVariance_pos_of_mass_one hp hmass).ne'
      field_simp [hvar]
      ring_nf

theorem objective_normalizeParam {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.Admissible p) (hmass : paramMass p = 1)
    (alpha : ℝ) :
    LogConcaveFamily6.objective alpha (normalizeParam p) =
      LogConcaveFamily6.integral
        (fun x ↦ LogConcaveClaimI.gAlpha alpha
          ((x - paramMean p) / paramSigma p)) p := by
  exact affineParam_integral (LogConcaveClaimI.gAlpha alpha) p
    (paramMean p) (paramSigma p) (paramSigma_pos_of_mass_one hp hmass)

/-! ## One decoder for every open-kink profile -/

def interiorOfOpen (u : OpenKinkProfile) (hl : 0 < u.l) (hr : 0 < u.r) :
    InteriorProfile where
  p := u.p
  l := u.l
  h := u.h
  r := u.r
  p_pos := u.p_pos
  p_lt_one := u.p_lt_one
  l_pos := hl
  h_pos := u.h_pos
  r_pos := hr
  concave := u.concave

/-- Raw mass-one parameter selected according to which endpoint profile
heights vanish. -/
def rawOpenParam (u : OpenKinkProfile) : LogConcaveFamily6.Param :=
  if hl : u.l = 0 then
    if hr : u.r = 0 then .wholeLine (rawWholeLine u)
    else .finiteRight (rawFiniteRight u)
  else if hr : u.r = 0 then .finiteLeft (rawFiniteLeft u)
  else .compact (rawCompact
    (interiorOfOpen u
      (lt_of_le_of_ne u.l_nonneg (Ne.symm hl))
      (lt_of_le_of_ne u.r_nonneg (Ne.symm hr))))

theorem rawOpenParam_admissible (u : OpenKinkProfile) :
    LogConcaveFamily6.Admissible (rawOpenParam u) := by
  by_cases hl : u.l = 0
  · by_cases hr : u.r = 0
    · simpa [rawOpenParam, hl, hr, LogConcaveFamily6.Admissible] using
        rawWholeLine_admissible u hl hr
    · simpa [rawOpenParam, hl, hr, LogConcaveFamily6.Admissible] using
        rawFiniteRight_admissible u hl
        (lt_of_le_of_ne u.r_nonneg (Ne.symm hr))
  · by_cases hr : u.r = 0
    · simpa [rawOpenParam, hl, hr, LogConcaveFamily6.Admissible] using
        rawFiniteLeft_admissible u
        (lt_of_le_of_ne u.l_nonneg (Ne.symm hl)) hr
    · simpa [rawOpenParam, hl, hr, LogConcaveFamily6.Admissible] using
        rawCompact_admissible (interiorOfOpen u
          (lt_of_le_of_ne u.l_nonneg (Ne.symm hl))
          (lt_of_le_of_ne u.r_nonneg (Ne.symm hr)))

theorem rawOpenParam_mass (u : OpenKinkProfile) :
    paramMass (rawOpenParam u) = 1 := by
  by_cases hl : u.l = 0
  · by_cases hr : u.r = 0
    · simpa [rawOpenParam, hl, hr, paramMass, LogConcaveFamily6.integral] using
        rawWholeLine_mass u hl hr
    · simpa [rawOpenParam, hl, hr, paramMass, LogConcaveFamily6.integral] using
        rawFiniteRight_mass u hl
        (lt_of_le_of_ne u.r_nonneg (Ne.symm hr))
  · by_cases hr : u.r = 0
    · simpa [rawOpenParam, hl, hr, paramMass, LogConcaveFamily6.integral] using
        rawFiniteLeft_mass u
        (lt_of_le_of_ne u.l_nonneg (Ne.symm hl)) hr
    · simpa [rawOpenParam, hl, hr, paramMass, LogConcaveFamily6.integral] using
        rawCompact_mass (interiorOfOpen u
          (lt_of_le_of_ne u.l_nonneg (Ne.symm hl))
          (lt_of_le_of_ne u.r_nonneg (Ne.symm hr)))

/-- The exact isotropic family-(6) member reconstructed from any concave
one-kink profile with `0<p<1`. -/
def decodeOpenKink (u : OpenKinkProfile) : LogConcaveFamily6.Param :=
  normalizeParam (rawOpenParam u)

theorem decodeOpenKink_mem_family6 (u : OpenKinkProfile) :
    decodeOpenKink u ∈ LogConcaveFamily6.family6 := by
  exact normalizeParam_mem_family6 (rawOpenParam_admissible u)
    (rawOpenParam_mass u)

/-- Objective in raw profile coordinates.  This is the exact target for the
remaining quantile substitution: on each affine profile segment one has
`dx = dt / I(t)`, while the density equals `I(t)`. -/
def openProfileObjective (alpha : ℝ) (u : OpenKinkProfile) : ℝ :=
  LogConcaveFamily6.integral
    (fun x ↦ LogConcaveClaimI.gAlpha alpha
      ((x - paramMean (rawOpenParam u)) / paramSigma (rawOpenParam u)))
    (rawOpenParam u)

theorem objective_decodeOpenKink (alpha : ℝ) (u : OpenKinkProfile) :
    LogConcaveFamily6.objective alpha (decodeOpenKink u) =
      openProfileObjective alpha u := by
  exact objective_normalizeParam (rawOpenParam_admissible u)
    (rawOpenParam_mass u) alpha

/-! ## Affine composition and exact recovery of an isotropic parameter -/

theorem affineParam_comp (p : LogConcaveFamily6.Param)
    (mu sigma nu tau : ℝ) (hsigma : 0 < sigma) (htau : 0 < tau) :
    affineParam (affineParam p mu sigma) nu tau =
      affineParam p (mu + sigma * nu) (sigma * tau) := by
  cases p with
  | compact u =>
      change LogConcaveFamily6.Param.compact
        (affineCompact (affineCompact u mu sigma) nu tau) =
        LogConcaveFamily6.Param.compact
          (affineCompact u (mu + sigma * nu) (sigma * tau))
      apply congrArg LogConcaveFamily6.Param.compact
      funext i
      fin_cases i
      · change affineCompact (affineCompact u mu sigma) nu tau 0 =
          affineCompact u (mu + sigma * nu) (sigma * tau) 0
        rw [affineCompact_zero, affineCompact_zero, affineCompact_zero]
        field_simp [hsigma.ne', htau.ne']
        ring_nf
      · change affineCompact (affineCompact u mu sigma) nu tau 1 =
          affineCompact u (mu + sigma * nu) (sigma * tau) 1
        rw [affineCompact_one, affineCompact_one, affineCompact_one]
        field_simp [hsigma.ne', htau.ne']
        ring_nf
      · change affineCompact (affineCompact u mu sigma) nu tau 2 =
          affineCompact u (mu + sigma * nu) (sigma * tau) 2
        rw [affineCompact_two, affineCompact_two, affineCompact_three,
          affineCompact_two, Real.log_mul hsigma.ne' htau.ne']
        ring
      · change affineCompact (affineCompact u mu sigma) nu tau 3 =
          affineCompact u (mu + sigma * nu) (sigma * tau) 3
        rw [affineCompact_three, affineCompact_three, affineCompact_three]
        ring
      · change affineCompact (affineCompact u mu sigma) nu tau 4 =
          affineCompact u (mu + sigma * nu) (sigma * tau) 4
        rw [affineCompact_four, affineCompact_four, affineCompact_four]
        ring
      · change affineCompact (affineCompact u mu sigma) nu tau 5 =
          affineCompact u (mu + sigma * nu) (sigma * tau) 5
        rw [affineCompact_five, affineCompact_five, affineCompact_five]
        field_simp [hsigma.ne', htau.ne']
        ring_nf
  | finiteLeft u =>
      change LogConcaveFamily6.Param.finiteLeft
        (affineHalfLine (affineHalfLine u mu sigma) nu tau) =
        LogConcaveFamily6.Param.finiteLeft
          (affineHalfLine u (mu + sigma * nu) (sigma * tau))
      apply congrArg LogConcaveFamily6.Param.finiteLeft
      funext i
      fin_cases i
      · change affineHalfLine (affineHalfLine u mu sigma) nu tau 0 =
          affineHalfLine u (mu + sigma * nu) (sigma * tau) 0
        rw [affineHalfLine_zero, affineHalfLine_zero, affineHalfLine_zero]
        field_simp [hsigma.ne', htau.ne']
        ring_nf
      · change affineHalfLine (affineHalfLine u mu sigma) nu tau 1 =
          affineHalfLine u (mu + sigma * nu) (sigma * tau) 1
        rw [affineHalfLine_one, affineHalfLine_one, affineHalfLine_two,
          affineHalfLine_one, Real.log_mul hsigma.ne' htau.ne']
        ring
      · change affineHalfLine (affineHalfLine u mu sigma) nu tau 2 =
          affineHalfLine u (mu + sigma * nu) (sigma * tau) 2
        rw [affineHalfLine_two, affineHalfLine_two, affineHalfLine_two]
        ring
      · change affineHalfLine (affineHalfLine u mu sigma) nu tau 3 =
          affineHalfLine u (mu + sigma * nu) (sigma * tau) 3
        rw [affineHalfLine_three, affineHalfLine_three, affineHalfLine_three]
        ring
      · change affineHalfLine (affineHalfLine u mu sigma) nu tau 4 =
          affineHalfLine u (mu + sigma * nu) (sigma * tau) 4
        rw [affineHalfLine_four, affineHalfLine_four, affineHalfLine_four]
        field_simp [hsigma.ne', htau.ne']
        ring_nf
  | finiteRight u =>
      change LogConcaveFamily6.Param.finiteRight
        (affineHalfLine (affineHalfLine u mu sigma) nu tau) =
        LogConcaveFamily6.Param.finiteRight
          (affineHalfLine u (mu + sigma * nu) (sigma * tau))
      apply congrArg LogConcaveFamily6.Param.finiteRight
      funext i
      fin_cases i
      · change affineHalfLine (affineHalfLine u mu sigma) nu tau 0 =
          affineHalfLine u (mu + sigma * nu) (sigma * tau) 0
        rw [affineHalfLine_zero, affineHalfLine_zero, affineHalfLine_zero]
        field_simp [hsigma.ne', htau.ne']
        ring_nf
      · change affineHalfLine (affineHalfLine u mu sigma) nu tau 1 =
          affineHalfLine u (mu + sigma * nu) (sigma * tau) 1
        rw [affineHalfLine_one, affineHalfLine_one, affineHalfLine_two,
          affineHalfLine_one, Real.log_mul hsigma.ne' htau.ne']
        ring
      · change affineHalfLine (affineHalfLine u mu sigma) nu tau 2 =
          affineHalfLine u (mu + sigma * nu) (sigma * tau) 2
        rw [affineHalfLine_two, affineHalfLine_two, affineHalfLine_two]
        ring
      · change affineHalfLine (affineHalfLine u mu sigma) nu tau 3 =
          affineHalfLine u (mu + sigma * nu) (sigma * tau) 3
        rw [affineHalfLine_three, affineHalfLine_three, affineHalfLine_three]
        ring
      · change affineHalfLine (affineHalfLine u mu sigma) nu tau 4 =
          affineHalfLine u (mu + sigma * nu) (sigma * tau) 4
        rw [affineHalfLine_four, affineHalfLine_four, affineHalfLine_four]
        field_simp [hsigma.ne', htau.ne']
        ring_nf
  | wholeLine u =>
      change LogConcaveFamily6.Param.wholeLine
        (affineWholeLine (affineWholeLine u mu sigma) nu tau) =
        LogConcaveFamily6.Param.wholeLine
          (affineWholeLine u (mu + sigma * nu) (sigma * tau))
      apply congrArg LogConcaveFamily6.Param.wholeLine
      cases u with
      | mk c beta delta m =>
          dsimp [affineWholeLine]
          congr 1
          all_goals try rw [Real.log_mul hsigma.ne' htau.ne']
          all_goals field_simp [hsigma.ne', htau.ne'] <;> ring_nf

theorem affineParam_zero_one (p : LogConcaveFamily6.Param) :
    affineParam p 0 1 = p := by
  cases p with
  | compact u =>
      change LogConcaveFamily6.Param.compact (affineCompact u 0 1) =
        LogConcaveFamily6.Param.compact u
      apply congrArg LogConcaveFamily6.Param.compact
      funext i
      fin_cases i
      · change affineCompact u 0 1 0 = u 0
        rw [affineCompact_zero]
        simp
      · change affineCompact u 0 1 1 = u 1
        rw [affineCompact_one]
        simp
      · change affineCompact u 0 1 2 = u 2
        rw [affineCompact_two]
        simp
      · change affineCompact u 0 1 3 = u 3
        rw [affineCompact_three]
        simp
      · change affineCompact u 0 1 4 = u 4
        rw [affineCompact_four]
        simp
      · change affineCompact u 0 1 5 = u 5
        rw [affineCompact_five]
        simp
  | finiteLeft u =>
      change LogConcaveFamily6.Param.finiteLeft (affineHalfLine u 0 1) =
        LogConcaveFamily6.Param.finiteLeft u
      apply congrArg LogConcaveFamily6.Param.finiteLeft
      funext i
      fin_cases i
      · change affineHalfLine u 0 1 0 = u 0
        rw [affineHalfLine_zero]
        simp
      · change affineHalfLine u 0 1 1 = u 1
        rw [affineHalfLine_one]
        simp
      · change affineHalfLine u 0 1 2 = u 2
        rw [affineHalfLine_two]
        simp
      · change affineHalfLine u 0 1 3 = u 3
        rw [affineHalfLine_three]
        simp
      · change affineHalfLine u 0 1 4 = u 4
        rw [affineHalfLine_four]
        simp
  | finiteRight u =>
      change LogConcaveFamily6.Param.finiteRight (affineHalfLine u 0 1) =
        LogConcaveFamily6.Param.finiteRight u
      apply congrArg LogConcaveFamily6.Param.finiteRight
      funext i
      fin_cases i
      · change affineHalfLine u 0 1 0 = u 0
        rw [affineHalfLine_zero]
        simp
      · change affineHalfLine u 0 1 1 = u 1
        rw [affineHalfLine_one]
        simp
      · change affineHalfLine u 0 1 2 = u 2
        rw [affineHalfLine_two]
        simp
      · change affineHalfLine u 0 1 3 = u 3
        rw [affineHalfLine_three]
        simp
      · change affineHalfLine u 0 1 4 = u 4
        rw [affineHalfLine_four]
        simp
  | wholeLine u =>
      change LogConcaveFamily6.Param.wholeLine (affineWholeLine u 0 1) =
        LogConcaveFamily6.Param.wholeLine u
      apply congrArg LogConcaveFamily6.Param.wholeLine
      cases u
      simp [affineWholeLine]

lemma paramMoments_of_isIsotropic {p : LogConcaveFamily6.Param}
    (hp : LogConcaveFamily6.IsIsotropic p) :
    paramMass p = 1 ∧ paramMean p = 0 ∧ paramSecondMoment p = 1 := by
  have h0 := congrFun hp (0 : Fin 3)
  have h1 := congrFun hp (1 : Fin 3)
  have h2 := congrFun hp (2 : Fin 3)
  constructor
  · simpa [paramMass, LogConcaveFamily6.momentMap,
      LogConcaveFamily6.isotropicTarget] using h0
  constructor
  · simpa [paramMean, LogConcaveFamily6.momentMap,
      LogConcaveFamily6.isotropicTarget] using h1
  · simpa [paramSecondMoment, LogConcaveFamily6.momentMap,
      LogConcaveFamily6.isotropicTarget] using h2

theorem normalizeParam_affine_of_isotropic {p : LogConcaveFamily6.Param}
    (hp : p ∈ LogConcaveFamily6.family6) (mu sigma : ℝ)
    (hsigma : 0 < sigma) :
    normalizeParam (affineParam p mu sigma) = p := by
  rcases paramMoments_of_isIsotropic hp.2 with ⟨hmass, hmean, hsecond⟩
  let q := affineParam p mu sigma
  have hqadm := affineParam_admissible (mu := mu) hp.1 hsigma
  have hqmass : paramMass q = 1 := by
    rw [affineParam_mass p mu sigma hsigma, hmass]
  have hqmean : paramMean q = -mu / sigma := by
    rw [affineParam_firstMoment hp.1 mu sigma hsigma, hmean, hmass]
    ring
  have hqsecond : paramSecondMoment q = (1 + mu ^ 2) / sigma ^ 2 := by
    rw [affineParam_secondMoment hp.1 mu sigma hsigma, hsecond, hmean, hmass]
    ring
  have hqvar : paramVariance q = 1 / sigma ^ 2 := by
    unfold paramVariance
    rw [hqmean, hqsecond]
    field_simp [hsigma.ne']
    ring
  have hqsigma : paramSigma q = 1 / sigma := by
    rw [paramSigma, hqvar]
    have hsquare : 1 / sigma ^ 2 = (1 / sigma) ^ 2 := by
      field_simp [hsigma.ne']
    rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < 1 / sigma)]
  unfold normalizeParam
  rw [hqmean, hqsigma, affineParam_comp p mu sigma (-mu / sigma) (1 / sigma)
    hsigma (by positivity)]
  convert affineParam_zero_one p using 1 <;> field_simp [hsigma.ne'] <;> ring_nf

end LogConcaveFamily6.ProfileDecode

end FlattenedExistenceSection7


/-!
Flattened source section: ProfileEncode.lean
-/

section FlattenedExistenceSection8

/-!
# Encoding family (6) by normalized quantile-density profiles

This file proves the encoding half of the profile compactification.  The
four coordinates are the probability mass to the left of the kink and the
three density heights, divided by their positive maximum.
-/



open Real Set MeasureTheory intervalIntegral
open scoped Interval

namespace LogConcaveFamily6.ProfileEncode

open LogConcaveClaimI
open LogConcaveFamily6.ProfileCompactification
open LogConcaveFamily6.ProfileDecode

/-! ## Elementary integral identities -/

lemma compact_left_mass_pos {p : CompactParam} (hAm : p 0 < p 5) :
    0 < leftIntegral (fun _ : ℝ ↦ 1) p := by
  unfold leftIntegral leftIntegrand
  apply intervalIntegral.integral_pos hAm
  · exact (show Continuous (fun x : ℝ ↦
        (1 : ℝ) * exp (leftExponent p x)) by
          unfold leftExponent
          fun_prop).continuousOn
  · intro x _
    simpa using (exp_pos (leftExponent p x)).le
  · exact ⟨p 0, ⟨le_rfl, hAm.le⟩, by
      simpa using exp_pos (leftExponent p (p 0))⟩

lemma compact_right_mass_pos {p : CompactParam} (hmB : p 5 < p 1) :
    0 < rightIntegral (fun _ : ℝ ↦ 1) p := by
  unfold rightIntegral rightIntegrand
  apply intervalIntegral.integral_pos hmB
  · exact (show Continuous (fun x : ℝ ↦
        (1 : ℝ) * exp (rightExponent p x)) by
          unfold rightExponent
          fun_prop).continuousOn
  · intro x _
    simpa using (exp_pos (rightExponent p x)).le
  · exact ⟨p 5, ⟨le_rfl, hmB.le⟩, by
      simpa using exp_pos (rightExponent p (p 5))⟩

lemma compact_left_height_difference (p : CompactParam) :
    p 3 * leftIntegral (fun _ : ℝ ↦ 1) p =
      exp (leftExponent p (p 5)) - exp (leftExponent p (p 0)) := by
  unfold leftIntegral leftIntegrand
  simp only [one_mul]
  change p 3 * (∫ x in p 0..p 5, exp (p 2 + p 3 * x)) =
    exp (p 2 + p 3 * p 5) - exp (p 2 + p 3 * p 0)
  by_cases hs : p 3 = 0
  · rw [hs]
    ring_nf
  · rw [ProfileDecode.integral_exp_affine_of_ne (p 2) (p 3) (p 0) (p 5) hs]
    field_simp [hs]

lemma compact_right_height_difference (p : CompactParam) :
    (p 3 - p 4) * rightIntegral (fun _ : ℝ ↦ 1) p =
      exp (rightExponent p (p 1)) - exp (rightExponent p (p 5)) := by
  unfold rightIntegral rightIntegrand
  let c : ℝ := p 2 + p 4 * p 5
  let s : ℝ := p 3 - p 4
  have hexp : ∀ x : ℝ, rightExponent p x = c + s * x := by
    intro x
    simp [rightExponent, c, s]
    ring
  by_cases hs : s = 0
  · simp only [one_mul]
    rw [show p 3 - p 4 = 0 by exact hs]
    simp only [zero_mul]
    rw [hexp (p 1), hexp (p 5), hs]
    ring_nf
  · simp only [one_mul]
    have hi := ProfileDecode.integral_exp_affine_of_ne c s (p 5) (p 1) hs
    rw [show (∫ x in p 5..p 1, exp (rightExponent p x)) =
        ∫ x in p 5..p 1, exp (c + s * x) by
          apply intervalIntegral.integral_congr
          intro x _
          change exp (rightExponent p x) = exp (c + s * x)
          rw [hexp x], hi]
    rw [hexp (p 1), hexp (p 5)]
    change s * ((exp (c + s * p 1) - exp (c + s * p 5)) / s) = _
    field_simp [hs]

/-! ## Compact-support encoder -/

def compactKinkMass (p : CompactParam) : ℝ :=
  leftIntegral (fun _ : ℝ ↦ 1) p

def compactLeftHeight (p : CompactParam) : ℝ :=
  exp (leftExponent p (p 0))

def compactKinkHeight (p : CompactParam) : ℝ :=
  exp (leftExponent p (p 5))

def compactRightHeight (p : CompactParam) : ℝ :=
  exp (rightExponent p (p 1))

def compactHeightScale (p : CompactParam) : ℝ :=
  max (compactLeftHeight p)
    (max (compactKinkHeight p) (compactRightHeight p))

lemma compactHeightScale_pos (p : CompactParam) : 0 < compactHeightScale p := by
  exact (exp_pos _).trans_le (le_max_left _ _)

def compactOpenProfile (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1) : OpenKinkProfile where
  p := compactKinkMass p
  l := compactLeftHeight p / compactHeightScale p
  h := compactKinkHeight p / compactHeightScale p
  r := compactRightHeight p / compactHeightScale p
  p_pos := compact_left_mass_pos hadm.1
  p_lt_one := by
    have hr := compact_right_mass_pos hadm.2.1
    unfold compactIntegral at hmass
    unfold compactKinkMass
    linarith
  l_nonneg := div_nonneg (exp_pos _).le (compactHeightScale_pos p).le
  h_pos := div_pos (exp_pos _) (compactHeightScale_pos p)
  r_nonneg := div_nonneg (exp_pos _).le (compactHeightScale_pos p).le
  concave := by
    have hl := compact_left_height_difference p
    have hr := compact_right_height_difference p
    have hsum : rightIntegral (fun _ : ℝ ↦ 1) p =
        1 - leftIntegral (fun _ : ℝ ↦ 1) p := by
      unfold compactIntegral at hmass
      linarith
    rw [hsum] at hr
    unfold compactKinkMass compactLeftHeight compactKinkHeight
      compactRightHeight
    have hkink : rightExponent p (p 5) = leftExponent p (p 5) := by
      simp [rightExponent, leftExponent]
    calc
      (1 - leftIntegral (fun _ : ℝ ↦ 1) p) *
            (exp (leftExponent p (p 0)) / compactHeightScale p) +
          leftIntegral (fun _ : ℝ ↦ 1) p *
            (exp (rightExponent p (p 1)) / compactHeightScale p) =
          ((1 - leftIntegral (fun _ : ℝ ↦ 1) p) *
              exp (leftExponent p (p 0)) +
            leftIntegral (fun _ : ℝ ↦ 1) p *
              exp (rightExponent p (p 1))) / compactHeightScale p := by ring
      _ ≤ exp (leftExponent p (p 5)) / compactHeightScale p := by
        apply (div_le_div_iff_of_pos_right (compactHeightScale_pos p)).2
        rw [hkink] at hr
        have ht0 : 0 ≤ leftIntegral (fun _ : ℝ ↦ 1) p :=
          (compact_left_mass_pos hadm.1).le
        have ht1 : 0 ≤ 1 - leftIntegral (fun _ : ℝ ↦ 1) p := by
          linarith [compact_right_mass_pos hadm.2.1]
        have hprod : 0 ≤ p 4 *
            (leftIntegral (fun _ : ℝ ↦ 1) p *
              (1 - leftIntegral (fun _ : ℝ ↦ 1) p)) :=
          mul_nonneg hadm.2.2 (mul_nonneg ht0 ht1)
        have hid :
            (1 - leftIntegral (fun _ : ℝ ↦ 1) p) *
                exp (leftExponent p (p 0)) +
              leftIntegral (fun _ : ℝ ↦ 1) p *
                exp (rightExponent p (p 1)) =
              exp (leftExponent p (p 5)) - p 4 *
                (leftIntegral (fun _ : ℝ ↦ 1) p *
                  (1 - leftIntegral (fun _ : ℝ ↦ 1) p)) := by
          nlinarith [hl, hr]
        rw [hid]
        exact sub_le_self _ hprod

/-- Forget the proof fields of an open-kink profile and retain its four
coordinates. -/
def openProfileParam (u : OpenKinkProfile) : ProfileParam :=
  ![u.p, u.l, u.h, u.r]

@[simp] lemma openProfileParam_zero (u : OpenKinkProfile) :
    openProfileParam u 0 = u.p := rfl

@[simp] lemma openProfileParam_one (u : OpenKinkProfile) :
    openProfileParam u 1 = u.l := rfl

@[simp] lemma openProfileParam_two (u : OpenKinkProfile) :
    openProfileParam u 2 = u.h := rfl

@[simp] lemma openProfileParam_three (u : OpenKinkProfile) :
    openProfileParam u 3 = u.r := rfl

lemma openProfileParam_mem_normalizedProfiles (u : OpenKinkProfile)
    (hnorm : max u.l (max u.h u.r) = 1) :
    openProfileParam u ∈ normalizedProfiles := by
  have hl1 : u.l ≤ 1 := by
    rw [← hnorm]
    exact le_max_left _ _
  have hh1 : u.h ≤ 1 := by
    rw [← hnorm]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hr1 : u.r ≤ 1 := by
    rw [← hnorm]
    exact (le_max_right _ _).trans (le_max_right _ _)
  constructor
  · intro i _
    fin_cases i
    · exact ⟨u.p_pos.le, u.p_lt_one.le⟩
    · exact ⟨u.l_nonneg, hl1⟩
    · exact ⟨u.h_pos.le, hh1⟩
    · exact ⟨u.r_nonneg, hr1⟩
  · constructor
    · exact u.concave
    · exact hnorm

lemma compactOpenProfile_normalized
    (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1) :
    max (compactOpenProfile p hadm hmass).l
      (max (compactOpenProfile p hadm hmass).h
        (compactOpenProfile p hadm hmass).r) = 1 := by
  change max (compactLeftHeight p / compactHeightScale p)
      (max (compactKinkHeight p / compactHeightScale p)
        (compactRightHeight p / compactHeightScale p)) = 1
  rw [max_div_div_right (compactHeightScale_pos p).le,
    max_div_div_right (compactHeightScale_pos p).le]
  change compactHeightScale p / compactHeightScale p = 1
  exact div_self (compactHeightScale_pos p).ne'

def compactProfileParam
    (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1) : ProfileParam :=
  openProfileParam (compactOpenProfile p hadm hmass)

theorem compactProfileParam_mem_normalizedProfiles
    (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1) :
    compactProfileParam p hadm hmass ∈ normalizedProfiles :=
  openProfileParam_mem_normalizedProfiles _
    (compactOpenProfile_normalized p hadm hmass)

/-! ## Finite-left support -/

lemma finiteLeft_left_mass_pos {p : HalfLineParam} (hAm : p 0 < p 4) :
    0 < halfLineLeftIntegral (fun _ : ℝ ↦ 1) p := by
  unfold halfLineLeftIntegral halfLineLeftIntegrand
  apply intervalIntegral.integral_pos hAm
  · exact (show Continuous (fun x : ℝ ↦
        (1 : ℝ) * exp (halfLineLeftExponent p x)) by
          unfold halfLineLeftExponent
          fun_prop).continuousOn
  · intro x _
    simpa using (exp_pos (halfLineLeftExponent p x)).le
  · exact ⟨p 0, ⟨le_rfl, hAm.le⟩, by
      simpa using exp_pos (halfLineLeftExponent p (p 0))⟩

lemma finiteLeft_left_height_difference (p : HalfLineParam) :
    p 2 * halfLineLeftIntegral (fun _ : ℝ ↦ 1) p =
      exp (halfLineLeftExponent p (p 4)) -
        exp (halfLineLeftExponent p (p 0)) := by
  unfold halfLineLeftIntegral halfLineLeftIntegrand
  simp only [one_mul]
  change p 2 * (∫ x in p 0..p 4, exp (p 1 + p 2 * x)) =
    exp (p 1 + p 2 * p 4) - exp (p 1 + p 2 * p 0)
  by_cases hs : p 2 = 0
  · rw [hs]
    ring_nf
  · rw [ProfileDecode.integral_exp_affine_of_ne
      (p 1) (p 2) (p 0) (p 4) hs]
    field_simp [hs]

lemma finiteLeft_right_mass_formula {p : HalfLineParam}
    (hs : p 2 - p 3 < 0) :
    halfLineRightIntegral (fun _ : ℝ ↦ 1) p =
      -exp (halfLineRightExponent p (p 4)) / (p 2 - p 3) := by
  unfold halfLineRightIntegral halfLineRightIntegrand
  simp only [one_mul]
  let c : ℝ := p 1 + p 3 * p 4
  let s : ℝ := p 2 - p 3
  have hexp : ∀ x : ℝ, halfLineRightExponent p x = c + s * x := by
    intro x
    simp [halfLineRightExponent, c, s]
    ring
  calc
    (∫ x : ℝ in Ioi (p 4), exp (halfLineRightExponent p x)) =
        ∫ x : ℝ in Ioi (p 4), exp (c + s * x) := by
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro x _
          change exp (halfLineRightExponent p x) = exp (c + s * x)
          rw [hexp x]
    _ = -exp (c + s * p 4) / s :=
      ProfileDecode.integral_exp_affine_Ioi c s (p 4) hs
    _ = _ := by rw [hexp (p 4)]

lemma finiteLeft_right_height_difference {p : HalfLineParam}
    (hs : p 2 - p 3 < 0) :
    (p 2 - p 3) * halfLineRightIntegral (fun _ : ℝ ↦ 1) p =
      -exp (halfLineRightExponent p (p 4)) := by
  rw [finiteLeft_right_mass_formula hs]
  field_simp [hs.ne]

lemma finiteLeft_right_mass_pos {p : HalfLineParam}
    (hs : p 2 - p 3 < 0) :
    0 < halfLineRightIntegral (fun _ : ℝ ↦ 1) p := by
  rw [finiteLeft_right_mass_formula hs]
  exact div_pos_of_neg_of_neg (neg_neg_of_pos (exp_pos _)) hs

def finiteLeftKinkMass (p : HalfLineParam) : ℝ :=
  halfLineLeftIntegral (fun _ : ℝ ↦ 1) p

def finiteLeftLeftHeight (p : HalfLineParam) : ℝ :=
  exp (halfLineLeftExponent p (p 0))

def finiteLeftKinkHeight (p : HalfLineParam) : ℝ :=
  exp (halfLineLeftExponent p (p 4))

def finiteLeftHeightScale (p : HalfLineParam) : ℝ :=
  max (finiteLeftLeftHeight p) (finiteLeftKinkHeight p)

lemma finiteLeftHeightScale_pos (p : HalfLineParam) :
    0 < finiteLeftHeightScale p :=
  (exp_pos _).trans_le (le_max_left _ _)

def finiteLeftOpenProfile (p : HalfLineParam)
    (hadm : p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0)
    (hmass : halfLineIntegral (fun _ : ℝ ↦ 1) p = 1) :
    OpenKinkProfile where
  p := finiteLeftKinkMass p
  l := finiteLeftLeftHeight p / finiteLeftHeightScale p
  h := finiteLeftKinkHeight p / finiteLeftHeightScale p
  r := 0
  p_pos := finiteLeft_left_mass_pos hadm.1
  p_lt_one := by
    have hr := finiteLeft_right_mass_pos hadm.2.2
    unfold halfLineIntegral at hmass
    unfold finiteLeftKinkMass
    linarith
  l_nonneg := div_nonneg (exp_pos _).le (finiteLeftHeightScale_pos p).le
  h_pos := div_pos (exp_pos _) (finiteLeftHeightScale_pos p)
  r_nonneg := le_rfl
  concave := by
    have hl := finiteLeft_left_height_difference p
    have hr := finiteLeft_right_height_difference hadm.2.2
    have hsum : halfLineRightIntegral (fun _ : ℝ ↦ 1) p =
        1 - halfLineLeftIntegral (fun _ : ℝ ↦ 1) p := by
      unfold halfLineIntegral at hmass
      linarith
    rw [hsum] at hr
    have hkink : halfLineRightExponent p (p 4) =
        halfLineLeftExponent p (p 4) := by
      simp [halfLineRightExponent, halfLineLeftExponent]
    rw [hkink] at hr
    change (1 - halfLineLeftIntegral (fun _ : ℝ ↦ 1) p) *
        (exp (halfLineLeftExponent p (p 0)) / finiteLeftHeightScale p) +
      halfLineLeftIntegral (fun _ : ℝ ↦ 1) p * 0 ≤
        exp (halfLineLeftExponent p (p 4)) / finiteLeftHeightScale p
    simp only [mul_zero, add_zero]
    calc
      (1 - halfLineLeftIntegral (fun _ : ℝ ↦ 1) p) *
          (exp (halfLineLeftExponent p (p 0)) / finiteLeftHeightScale p) =
        ((1 - halfLineLeftIntegral (fun _ : ℝ ↦ 1) p) *
          exp (halfLineLeftExponent p (p 0))) / finiteLeftHeightScale p := by
            ring
      _ ≤ exp (halfLineLeftExponent p (p 4)) /
          finiteLeftHeightScale p := by
        apply (div_le_div_iff_of_pos_right (finiteLeftHeightScale_pos p)).2
        have ht0 := (finiteLeft_left_mass_pos hadm.1).le
        have ht1 : 0 ≤ 1 - halfLineLeftIntegral (fun _ : ℝ ↦ 1) p := by
          linarith [finiteLeft_right_mass_pos hadm.2.2]
        have hprod : 0 ≤ p 3 *
            (halfLineLeftIntegral (fun _ : ℝ ↦ 1) p *
              (1 - halfLineLeftIntegral (fun _ : ℝ ↦ 1) p)) :=
          mul_nonneg hadm.2.1 (mul_nonneg ht0 ht1)
        have hid :
            (1 - halfLineLeftIntegral (fun _ : ℝ ↦ 1) p) *
                exp (halfLineLeftExponent p (p 0)) =
              exp (halfLineLeftExponent p (p 4)) - p 3 *
                (halfLineLeftIntegral (fun _ : ℝ ↦ 1) p *
                  (1 - halfLineLeftIntegral (fun _ : ℝ ↦ 1) p)) := by
          nlinarith [hl, hr]
        rw [hid]
        exact sub_le_self _ hprod

lemma finiteLeftOpenProfile_normalized
    (p : HalfLineParam)
    (hadm : p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0)
    (hmass : halfLineIntegral (fun _ : ℝ ↦ 1) p = 1) :
    max (finiteLeftOpenProfile p hadm hmass).l
      (max (finiteLeftOpenProfile p hadm hmass).h
        (finiteLeftOpenProfile p hadm hmass).r) = 1 := by
  change max (finiteLeftLeftHeight p / finiteLeftHeightScale p)
      (max (finiteLeftKinkHeight p / finiteLeftHeightScale p) 0) = 1
  have hk0 : 0 ≤ finiteLeftKinkHeight p / finiteLeftHeightScale p := by
    exact div_nonneg (by exact (exp_pos _).le)
      (finiteLeftHeightScale_pos p).le
  rw [max_eq_left hk0]
  rw [max_div_div_right (finiteLeftHeightScale_pos p).le]
  change finiteLeftHeightScale p / finiteLeftHeightScale p = 1
  exact div_self (finiteLeftHeightScale_pos p).ne'

def finiteLeftProfileParam
    (p : HalfLineParam)
    (hadm : p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0)
    (hmass : halfLineIntegral (fun _ : ℝ ↦ 1) p = 1) : ProfileParam :=
  openProfileParam (finiteLeftOpenProfile p hadm hmass)

theorem finiteLeftProfileParam_mem_normalizedProfiles
    (p : HalfLineParam)
    (hadm : p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0)
    (hmass : halfLineIntegral (fun _ : ℝ ↦ 1) p = 1) :
    finiteLeftProfileParam p hadm hmass ∈ normalizedProfiles :=
  openProfileParam_mem_normalizedProfiles _
    (finiteLeftOpenProfile_normalized p hadm hmass)

/-! ## Finite-right support -/

lemma finiteRight_left_mass_formula {p : HalfLineParam} (hbeta : 0 < p 2) :
    finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p =
      exp (finiteRightLeftExponent p (p 4)) / p 2 := by
  unfold finiteRightLeftTailIntegral finiteRightLeftIntegrand
  simp only [one_mul]
  exact ProfileDecode.integral_exp_affine_Iic (p 1) (p 2) (p 4) hbeta

lemma finiteRight_left_height_difference {p : HalfLineParam}
    (hbeta : 0 < p 2) :
    p 2 * finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p =
      exp (finiteRightLeftExponent p (p 4)) := by
  rw [finiteRight_left_mass_formula hbeta]
  field_simp [hbeta.ne']

lemma finiteRight_left_mass_pos {p : HalfLineParam} (hbeta : 0 < p 2) :
    0 < finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p := by
  rw [finiteRight_left_mass_formula hbeta]
  exact div_pos (exp_pos _) hbeta

lemma finiteRight_right_mass_pos {p : HalfLineParam} (hmB : p 4 < p 0) :
    0 < finiteRightRightCompactIntegral (fun _ : ℝ ↦ 1) p := by
  unfold finiteRightRightCompactIntegral finiteRightRightIntegrand
  apply intervalIntegral.integral_pos hmB
  · exact (show Continuous (fun x : ℝ ↦
        (1 : ℝ) * exp (finiteRightRightExponent p x)) by
          unfold finiteRightRightExponent
          fun_prop).continuousOn
  · intro x _
    simpa using (exp_pos (finiteRightRightExponent p x)).le
  · exact ⟨p 4, ⟨le_rfl, hmB.le⟩, by
      simpa using exp_pos (finiteRightRightExponent p (p 4))⟩

lemma finiteRight_right_height_difference (p : HalfLineParam) :
    (p 2 - p 3) *
        finiteRightRightCompactIntegral (fun _ : ℝ ↦ 1) p =
      exp (finiteRightRightExponent p (p 0)) -
        exp (finiteRightRightExponent p (p 4)) := by
  unfold finiteRightRightCompactIntegral finiteRightRightIntegrand
  simp only [one_mul]
  let c : ℝ := p 1 + p 3 * p 4
  let s : ℝ := p 2 - p 3
  have hexp : ∀ x : ℝ, finiteRightRightExponent p x = c + s * x := by
    intro x
    simp [finiteRightRightExponent, c, s]
    ring
  by_cases hs : s = 0
  · rw [show p 2 - p 3 = 0 by exact hs]
    simp only [zero_mul]
    rw [hexp (p 0), hexp (p 4), hs]
    ring_nf
  · have hi := ProfileDecode.integral_exp_affine_of_ne c s (p 4) (p 0) hs
    rw [show (∫ x in p 4..p 0, exp (finiteRightRightExponent p x)) =
        ∫ x in p 4..p 0, exp (c + s * x) by
          apply intervalIntegral.integral_congr
          intro x _
          change exp (finiteRightRightExponent p x) = exp (c + s * x)
          rw [hexp x], hi]
    rw [hexp (p 0), hexp (p 4)]
    change s * ((exp (c + s * p 0) - exp (c + s * p 4)) / s) = _
    field_simp [hs]

def finiteRightKinkMass (p : HalfLineParam) : ℝ :=
  finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p

def finiteRightKinkHeight (p : HalfLineParam) : ℝ :=
  exp (finiteRightLeftExponent p (p 4))

def finiteRightRightHeight (p : HalfLineParam) : ℝ :=
  exp (finiteRightRightExponent p (p 0))

def finiteRightHeightScale (p : HalfLineParam) : ℝ :=
  max (finiteRightKinkHeight p) (finiteRightRightHeight p)

lemma finiteRightHeightScale_pos (p : HalfLineParam) :
    0 < finiteRightHeightScale p :=
  (exp_pos _).trans_le (le_max_left _ _)

def finiteRightOpenProfile (p : HalfLineParam)
    (hadm : p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2)
    (hmass : finiteRightActualIntegral (fun _ : ℝ ↦ 1) p = 1) :
    OpenKinkProfile where
  p := finiteRightKinkMass p
  l := 0
  h := finiteRightKinkHeight p / finiteRightHeightScale p
  r := finiteRightRightHeight p / finiteRightHeightScale p
  p_pos := finiteRight_left_mass_pos hadm.2.2
  p_lt_one := by
    have hr := finiteRight_right_mass_pos hadm.1
    unfold finiteRightActualIntegral at hmass
    unfold finiteRightKinkMass
    linarith
  l_nonneg := le_rfl
  h_pos := div_pos (exp_pos _) (finiteRightHeightScale_pos p)
  r_nonneg := div_nonneg (exp_pos _).le (finiteRightHeightScale_pos p).le
  concave := by
    have hl := finiteRight_left_height_difference hadm.2.2
    have hr := finiteRight_right_height_difference p
    have hsum : finiteRightRightCompactIntegral (fun _ : ℝ ↦ 1) p =
        1 - finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p := by
      unfold finiteRightActualIntegral at hmass
      linarith
    rw [hsum] at hr
    have hkink : finiteRightRightExponent p (p 4) =
        finiteRightLeftExponent p (p 4) := by
      simp [finiteRightRightExponent, finiteRightLeftExponent]
    rw [hkink] at hr
    change (1 - finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p) * 0 +
      finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p *
        (exp (finiteRightRightExponent p (p 0)) / finiteRightHeightScale p) ≤
      exp (finiteRightLeftExponent p (p 4)) / finiteRightHeightScale p
    simp only [mul_zero, zero_add]
    calc
      finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p *
          (exp (finiteRightRightExponent p (p 0)) / finiteRightHeightScale p) =
        (finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p *
          exp (finiteRightRightExponent p (p 0))) / finiteRightHeightScale p := by
            ring
      _ ≤ exp (finiteRightLeftExponent p (p 4)) /
          finiteRightHeightScale p := by
        apply (div_le_div_iff_of_pos_right (finiteRightHeightScale_pos p)).2
        have ht0 := (finiteRight_left_mass_pos hadm.2.2).le
        have ht1 : 0 ≤ 1 -
            finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p := by
          linarith [finiteRight_right_mass_pos hadm.1]
        have hprod : 0 ≤ p 3 *
            (finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p *
              (1 - finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p)) :=
          mul_nonneg hadm.2.1 (mul_nonneg ht0 ht1)
        have hid :
            finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p *
                exp (finiteRightRightExponent p (p 0)) =
              exp (finiteRightLeftExponent p (p 4)) - p 3 *
                (finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p *
                  (1 - finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p)) := by
          nlinarith [hl, hr]
        rw [hid]
        exact sub_le_self _ hprod

lemma finiteRightOpenProfile_normalized
    (p : HalfLineParam)
    (hadm : p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2)
    (hmass : finiteRightActualIntegral (fun _ : ℝ ↦ 1) p = 1) :
    max (finiteRightOpenProfile p hadm hmass).l
      (max (finiteRightOpenProfile p hadm hmass).h
        (finiteRightOpenProfile p hadm hmass).r) = 1 := by
  change max 0
      (max (finiteRightKinkHeight p / finiteRightHeightScale p)
        (finiteRightRightHeight p / finiteRightHeightScale p)) = 1
  have hinner0 : 0 ≤ max (finiteRightKinkHeight p / finiteRightHeightScale p)
      (finiteRightRightHeight p / finiteRightHeightScale p) :=
    (div_nonneg (exp_pos _).le (finiteRightHeightScale_pos p).le).trans
      (le_max_left _ _)
  rw [max_eq_right hinner0,
    max_div_div_right (finiteRightHeightScale_pos p).le]
  change finiteRightHeightScale p / finiteRightHeightScale p = 1
  exact div_self (finiteRightHeightScale_pos p).ne'

def finiteRightProfileParam
    (p : HalfLineParam)
    (hadm : p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2)
    (hmass : finiteRightActualIntegral (fun _ : ℝ ↦ 1) p = 1) : ProfileParam :=
  openProfileParam (finiteRightOpenProfile p hadm hmass)

theorem finiteRightProfileParam_mem_normalizedProfiles
    (p : HalfLineParam)
    (hadm : p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2)
    (hmass : finiteRightActualIntegral (fun _ : ℝ ↦ 1) p = 1) :
    finiteRightProfileParam p hadm hmass ∈ normalizedProfiles :=
  openProfileParam_mem_normalizedProfiles _
    (finiteRightOpenProfile_normalized p hadm hmass)

/-! ## Whole-line support -/

def wholeLineLeftMass (p : LogConcaveFamily6.WholeLineParam) : ℝ :=
  ∫ x : ℝ in Iic p.m, exp (p.c + p.beta * x)

def wholeLineRightMass (p : LogConcaveFamily6.WholeLineParam) : ℝ :=
  ∫ x : ℝ in Ioi p.m,
    exp (p.c + p.beta * x - p.delta * (x - p.m))

lemma wholeLine_left_mass_formula
    (p : LogConcaveFamily6.WholeLineParam) (hbeta : 0 < p.beta) :
    wholeLineLeftMass p = exp (p.c + p.beta * p.m) / p.beta := by
  exact ProfileDecode.integral_exp_affine_Iic p.c p.beta p.m hbeta

lemma wholeLine_left_mass_pos
    (p : LogConcaveFamily6.WholeLineParam) (hbeta : 0 < p.beta) :
    0 < wholeLineLeftMass p := by
  rw [wholeLine_left_mass_formula p hbeta]
  exact div_pos (exp_pos _) hbeta

lemma wholeLine_right_mass_formula
    (p : LogConcaveFamily6.WholeLineParam)
    (hs : p.beta - p.delta < 0) :
    wholeLineRightMass p =
      -exp (p.c + p.beta * p.m) / (p.beta - p.delta) := by
  let c : ℝ := p.c + p.delta * p.m
  let s : ℝ := p.beta - p.delta
  have hexp : ∀ x : ℝ,
      p.c + p.beta * x - p.delta * (x - p.m) = c + s * x := by
    intro x
    simp [c, s]
    ring
  calc
    wholeLineRightMass p =
        ∫ x : ℝ in Ioi p.m, exp (c + s * x) := by
          unfold wholeLineRightMass
          apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          intro x _
          change exp (p.c + p.beta * x - p.delta * (x - p.m)) =
            exp (c + s * x)
          rw [hexp x]
    _ = -exp (c + s * p.m) / s :=
      ProfileDecode.integral_exp_affine_Ioi c s p.m hs
    _ = _ := by
      have hm := hexp p.m
      simp only [sub_self, mul_zero, sub_zero] at hm
      rw [← hm]

lemma wholeLine_right_mass_pos
    (p : LogConcaveFamily6.WholeLineParam)
    (hs : p.beta - p.delta < 0) :
    0 < wholeLineRightMass p := by
  rw [wholeLine_right_mass_formula p hs]
  exact div_pos_of_neg_of_neg (neg_neg_of_pos (exp_pos _)) hs

def wholeLineOpenProfile (p : LogConcaveFamily6.WholeLineParam)
    (hadm : 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0)
    (hmass : wholeLineLeftMass p + wholeLineRightMass p = 1) :
    OpenKinkProfile where
  p := wholeLineLeftMass p
  l := 0
  h := 1
  r := 0
  p_pos := wholeLine_left_mass_pos p hadm.2.1
  p_lt_one := by linarith [wholeLine_right_mass_pos p hadm.2.2]
  l_nonneg := le_rfl
  h_pos := zero_lt_one
  r_nonneg := le_rfl
  concave := by
    change (1 - wholeLineLeftMass p) * 0 + wholeLineLeftMass p * 0 ≤ 1
    norm_num

lemma wholeLineOpenProfile_normalized
    (p : LogConcaveFamily6.WholeLineParam)
    (hadm : 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0)
    (hmass : wholeLineLeftMass p + wholeLineRightMass p = 1) :
    max (wholeLineOpenProfile p hadm hmass).l
      (max (wholeLineOpenProfile p hadm hmass).h
        (wholeLineOpenProfile p hadm hmass).r) = 1 := by
  change max 0 (max 1 0) = 1
  norm_num

def wholeLineProfileParam
    (p : LogConcaveFamily6.WholeLineParam)
    (hadm : 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0)
    (hmass : wholeLineLeftMass p + wholeLineRightMass p = 1) : ProfileParam :=
  openProfileParam (wholeLineOpenProfile p hadm hmass)

theorem wholeLineProfileParam_mem_normalizedProfiles
    (p : LogConcaveFamily6.WholeLineParam)
    (hadm : 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0)
    (hmass : wholeLineLeftMass p + wholeLineRightMass p = 1) :
    wholeLineProfileParam p hadm hmass ∈ normalizedProfiles :=
  openProfileParam_mem_normalizedProfiles _
    (wholeLineOpenProfile_normalized p hadm hmass)

/-! ## Tagged encoder -/

lemma mass_eq_one_of_isIsotropic {q : LogConcaveFamily6.Param}
    (hq : LogConcaveFamily6.IsIsotropic q) :
    LogConcaveFamily6.integral (fun _ : ℝ ↦ 1) q = 1 := by
  have h := congrFun hq (0 : Fin 3)
  simpa [LogConcaveFamily6.momentMap, LogConcaveFamily6.isotropicTarget] using h

def encodeOpenProfile (q : LogConcaveFamily6.Param)
    (hq : q ∈ LogConcaveFamily6.family6) : OpenKinkProfile := by
  rcases hq with ⟨hadm, hiso⟩
  have hmass := mass_eq_one_of_isIsotropic hiso
  cases q with
  | compact p =>
      exact compactOpenProfile p hadm hmass
  | finiteLeft p =>
      exact finiteLeftOpenProfile p hadm hmass
  | finiteRight p =>
      exact finiteRightOpenProfile p hadm hmass
  | wholeLine p =>
      have hmass' : wholeLineLeftMass p + wholeLineRightMass p = 1 := by
        simpa [LogConcaveFamily6.integral, wholeLineLeftMass,
          wholeLineRightMass] using hmass
      exact wholeLineOpenProfile p hadm hmass'

def encodeProfile (q : LogConcaveFamily6.Param)
    (hq : q ∈ LogConcaveFamily6.family6) : ProfileParam :=
  openProfileParam (encodeOpenProfile q hq)

theorem encodeProfile_mem_normalizedProfiles
    (q : LogConcaveFamily6.Param)
    (hq : q ∈ LogConcaveFamily6.family6) :
    encodeProfile q hq ∈ normalizedProfiles := by
  rcases hq with ⟨hadm, hiso⟩
  have hmass := mass_eq_one_of_isIsotropic hiso
  cases q with
  | compact p =>
      exact compactProfileParam_mem_normalizedProfiles p hadm hmass
  | finiteLeft p =>
      exact finiteLeftProfileParam_mem_normalizedProfiles p hadm hmass
  | finiteRight p =>
      exact finiteRightProfileParam_mem_normalizedProfiles p hadm hmass
  | wholeLine p =>
      have hmass' : wholeLineLeftMass p + wholeLineRightMass p = 1 := by
        simpa [LogConcaveFamily6.integral, wholeLineLeftMass,
          wholeLineRightMass] using hmass
      exact wholeLineProfileParam_mem_normalizedProfiles p hadm hmass'

theorem encodeProfile_kinkMass_pos
    (q : LogConcaveFamily6.Param)
    (hq : q ∈ LogConcaveFamily6.family6) :
    0 < kinkMass (encodeProfile q hq) :=
  (encodeOpenProfile q hq).p_pos

theorem encodeProfile_kinkMass_lt_one
    (q : LogConcaveFamily6.Param)
    (hq : q ∈ LogConcaveFamily6.family6) :
    kinkMass (encodeProfile q hq) < 1 :=
  (encodeOpenProfile q hq).p_lt_one

/-! ## Exact raw inverse: compact chart -/

lemma compactOpenProfile_leftSlope
    (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1) :
    openLeftSlope (compactOpenProfile p hadm hmass) =
      p 3 / compactHeightScale p := by
  have ht := (compact_left_mass_pos hadm.1).ne'
  have hM := (compactHeightScale_pos p).ne'
  have hd := compact_left_height_difference p
  change ((compactKinkHeight p / compactHeightScale p -
      compactLeftHeight p / compactHeightScale p) /
        compactKinkMass p) = p 3 / compactHeightScale p
  unfold compactKinkHeight compactLeftHeight compactKinkMass at ⊢
  field_simp [ht, hM]
  nlinarith

lemma compactOpenProfile_rightSlope
    (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1) :
    openRightSlope (compactOpenProfile p hadm hmass) =
      (p 3 - p 4) / compactHeightScale p := by
  have ht1 : 1 - leftIntegral (fun _ : ℝ ↦ 1) p ≠ 0 := by
    have hr := compact_right_mass_pos hadm.2.1
    unfold compactIntegral at hmass
    intro hz
    rw [← show rightIntegral (fun _ : ℝ ↦ 1) p =
      1 - leftIntegral (fun _ : ℝ ↦ 1) p by linarith] at hz
    linarith
  have hM := (compactHeightScale_pos p).ne'
  have hd := compact_right_height_difference p
  have hsum : rightIntegral (fun _ : ℝ ↦ 1) p =
      1 - leftIntegral (fun _ : ℝ ↦ 1) p := by
    unfold compactIntegral at hmass
    linarith
  rw [hsum] at hd
  have hkink : rightExponent p (p 5) = leftExponent p (p 5) := by
    simp [rightExponent, leftExponent]
  rw [hkink] at hd
  change ((compactRightHeight p / compactHeightScale p -
      compactKinkHeight p / compactHeightScale p) /
        (1 - compactKinkMass p)) =
      (p 3 - p 4) / compactHeightScale p
  unfold compactRightHeight compactKinkHeight compactKinkMass at ⊢
  field_simp [ht1, hM]
  nlinarith

lemma compact_left_mass_of_zero_slope
    (p : CompactParam) (hbeta : p 3 = 0) :
    leftIntegral (fun _ : ℝ ↦ 1) p =
      exp (leftExponent p (p 0)) * (p 5 - p 0) := by
  unfold leftIntegral leftIntegrand leftExponent
  simp [hbeta]
  ring

lemma compactOpenProfile_leftLength
    (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1) :
    openLeftLength (compactOpenProfile p hadm hmass) =
      compactHeightScale p * (p 5 - p 0) := by
  let u := compactOpenProfile p hadm hmass
  have hM := compactHeightScale_pos p
  have ht := compact_left_mass_pos hadm.1
  have hsl := compactOpenProfile_leftSlope p hadm hmass
  unfold openLeftLength
  by_cases hbeta : p 3 = 0
  · have hs : openLeftSlope u = 0 := by rw [hsl, hbeta, zero_div]
    rw [if_pos hs]
    have hm := compact_left_mass_of_zero_slope p hbeta
    change compactKinkMass p /
        (compactLeftHeight p / compactHeightScale p) = _
    unfold compactKinkMass compactLeftHeight
    rw [hm]
    field_simp [hM.ne']
  · have hs : openLeftSlope u ≠ 0 := by
      rw [hsl]
      exact div_ne_zero hbeta hM.ne'
    rw [if_neg hs, hsl]
    change log ((compactKinkHeight p / compactHeightScale p) /
        (compactLeftHeight p / compactHeightScale p)) /
          (p 3 / compactHeightScale p) = _
    have hratio :
        (compactKinkHeight p / compactHeightScale p) /
            (compactLeftHeight p / compactHeightScale p) =
          exp (p 3 * (p 5 - p 0)) := by
      unfold compactKinkHeight compactLeftHeight leftExponent
      calc
        exp (p 2 + p 3 * p 5) / compactHeightScale p /
            (exp (p 2 + p 3 * p 0) / compactHeightScale p) =
          exp (p 2 + p 3 * p 5) / exp (p 2 + p 3 * p 0) := by
            field_simp [hM.ne', (exp_pos (p 2 + p 3 * p 0)).ne']
        _ = exp ((p 2 + p 3 * p 5) - (p 2 + p 3 * p 0)) := by
          rw [Real.exp_sub]
        _ = exp (p 3 * (p 5 - p 0)) := by congr 1 <;> ring
    rw [hratio, Real.log_exp]
    field_simp [hbeta, hM.ne']

lemma compact_right_mass_of_zero_slope
    (p : CompactParam) (hslope : p 3 - p 4 = 0) :
    rightIntegral (fun _ : ℝ ↦ 1) p =
      exp (rightExponent p (p 5)) * (p 1 - p 5) := by
  unfold rightIntegral rightIntegrand
  simp only [one_mul]
  have hconst : ∀ x : ℝ,
      rightExponent p x = rightExponent p (p 5) := by
    intro x
    have heq : p 3 = p 4 := by linarith
    unfold rightExponent
    rw [heq]
    ring
  calc
    (∫ x in p 5..p 1, exp (rightExponent p x)) =
        ∫ _x in p 5..p 1, exp (rightExponent p (p 5)) := by
          apply intervalIntegral.integral_congr
          intro x _
          change exp (rightExponent p x) = exp (rightExponent p (p 5))
          rw [hconst x]
    _ = _ := by simp; ring

lemma compactOpenProfile_rightLength
    (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1) :
    openRightLength (compactOpenProfile p hadm hmass) =
      compactHeightScale p * (p 1 - p 5) := by
  let u := compactOpenProfile p hadm hmass
  have hM := compactHeightScale_pos p
  have hsr := compactOpenProfile_rightSlope p hadm hmass
  unfold openRightLength
  by_cases hslope : p 3 - p 4 = 0
  · have hs : openRightSlope u = 0 := by rw [hsr, hslope, zero_div]
    rw [if_pos hs]
    have hm := compact_right_mass_of_zero_slope p hslope
    have hsum : 1 - compactKinkMass p =
        rightIntegral (fun _ : ℝ ↦ 1) p := by
      unfold compactKinkMass
      unfold compactIntegral at hmass
      linarith
    change (1 - compactKinkMass p) /
        (compactKinkHeight p / compactHeightScale p) = _
    rw [hsum, hm]
    have hkink : rightExponent p (p 5) = leftExponent p (p 5) := by
      simp [rightExponent, leftExponent]
    unfold compactKinkHeight
    rw [hkink]
    field_simp [hM.ne']
  · have hs : openRightSlope u ≠ 0 := by
      rw [hsr]
      exact div_ne_zero hslope hM.ne'
    rw [if_neg hs, hsr]
    change log ((compactRightHeight p / compactHeightScale p) /
        (compactKinkHeight p / compactHeightScale p)) /
          ((p 3 - p 4) / compactHeightScale p) = _
    have hratio :
        (compactRightHeight p / compactHeightScale p) /
            (compactKinkHeight p / compactHeightScale p) =
          exp ((p 3 - p 4) * (p 1 - p 5)) := by
      unfold compactRightHeight compactKinkHeight rightExponent leftExponent
      calc
        exp (p 2 + p 3 * p 1 - p 4 * (p 1 - p 5)) /
              compactHeightScale p /
            (exp (p 2 + p 3 * p 5) / compactHeightScale p) =
          exp (p 2 + p 3 * p 1 - p 4 * (p 1 - p 5)) /
            exp (p 2 + p 3 * p 5) := by
              field_simp [hM.ne', (exp_pos (p 2 + p 3 * p 5)).ne']
        _ = exp ((p 2 + p 3 * p 1 - p 4 * (p 1 - p 5)) -
            (p 2 + p 3 * p 5)) := by
              exact (Real.exp_sub _ _).symm
        _ = exp ((p 3 - p 4) * (p 1 - p 5)) := by congr 1 <;> ring
    rw [hratio, Real.log_exp]
    field_simp [hslope, hM.ne']

lemma compactOpenProfile_log_left
    (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1) :
    log (compactOpenProfile p hadm hmass).l =
      log (1 / compactHeightScale p) + p 2 + p 3 * p 0 := by
  have hM := compactHeightScale_pos p
  change log (exp (leftExponent p (p 0)) / compactHeightScale p) = _
  rw [Real.log_div (exp_pos _).ne' hM.ne', Real.log_exp]
  have hinv : log (1 / compactHeightScale p) = -log (compactHeightScale p) := by
    rw [one_div, Real.log_inv]
  rw [hinv]
  unfold leftExponent
  ring

def compactInteriorProfile
    (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1) : InteriorProfile :=
  interiorOfOpen (compactOpenProfile p hadm hmass)
    (div_pos (exp_pos _) (compactHeightScale_pos p))
    (div_pos (exp_pos _) (compactHeightScale_pos p))

theorem rawCompact_compactOpenProfile
    (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1) :
    rawCompact (compactInteriorProfile p hadm hmass) =
      affineCompact p (p 0) (1 / compactHeightScale p) := by
  let u := compactOpenProfile p hadm hmass
  let v := compactInteriorProfile p hadm hmass
  have hleftSlope : leftSlope v = p 3 / compactHeightScale p := by
    change openLeftSlope u = p 3 / compactHeightScale p
    exact compactOpenProfile_leftSlope p hadm hmass
  have hrightSlope : rightSlope v =
      (p 3 - p 4) / compactHeightScale p := by
    change openRightSlope u = (p 3 - p 4) / compactHeightScale p
    exact compactOpenProfile_rightSlope p hadm hmass
  have hleftLength : leftLength v =
      compactHeightScale p * (p 5 - p 0) := by
    change openLeftLength u = compactHeightScale p * (p 5 - p 0)
    exact compactOpenProfile_leftLength p hadm hmass
  have hrightLength : rightLength v =
      compactHeightScale p * (p 1 - p 5) := by
    change openRightLength u = compactHeightScale p * (p 1 - p 5)
    exact compactOpenProfile_rightLength p hadm hmass
  have hlog : log v.l =
      log (1 / compactHeightScale p) + p 2 + p 3 * p 0 := by
    change log u.l = _
    exact compactOpenProfile_log_left p hadm hmass
  funext i
  fin_cases i
  · simp [rawCompact, affineCompact]
  · change leftLength v + rightLength v =
      (p 1 - p 0) / (1 / compactHeightScale p)
    rw [hleftLength, hrightLength]
    field_simp [(compactHeightScale_pos p).ne']
    ring_nf
  · simpa [rawCompact, affineCompact] using hlog
  · change leftSlope v = p 3 * (1 / compactHeightScale p)
    rw [hleftSlope]
    ring
  · change leftSlope v - rightSlope v = p 4 * (1 / compactHeightScale p)
    rw [hleftSlope, hrightSlope]
    field_simp [(compactHeightScale_pos p).ne']
    ring_nf
  · change leftLength v = (p 5 - p 0) / (1 / compactHeightScale p)
    rw [hleftLength]
    field_simp [(compactHeightScale_pos p).ne']

theorem rawOpenParam_compactOpenProfile
    (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hmass : compactIntegral (fun _ : ℝ ↦ 1) p = 1) :
    rawOpenParam (compactOpenProfile p hadm hmass) =
      affineParam (.compact p) (p 0) (1 / compactHeightScale p) := by
  let u := compactOpenProfile p hadm hmass
  have hl : u.l ≠ 0 :=
    (div_pos (exp_pos _) (compactHeightScale_pos p)).ne'
  have hr : u.r ≠ 0 :=
    (div_pos (exp_pos _) (compactHeightScale_pos p)).ne'
  change rawOpenParam u =
    affineParam (.compact p) (p 0) (1 / compactHeightScale p)
  rw [rawOpenParam, dif_neg hl, dif_neg hr]
  change LogConcaveFamily6.Param.compact
      (rawCompact (compactInteriorProfile p hadm hmass)) =
    LogConcaveFamily6.Param.compact
      (affineCompact p (p 0) (1 / compactHeightScale p))
  rw [rawCompact_compactOpenProfile p hadm hmass]

theorem decodeOpenKink_compactOpenProfile
    (p : CompactParam)
    (hadm : p 0 < p 5 ∧ p 5 < p 1 ∧ 0 ≤ p 4)
    (hiso : LogConcaveFamily6.IsIsotropic (.compact p)) :
    decodeOpenKink
        (compactOpenProfile p hadm (mass_eq_one_of_isIsotropic hiso)) =
      .compact p := by
  let hp : LogConcaveFamily6.Param := .compact p
  have hpfam : hp ∈ LogConcaveFamily6.family6 := ⟨hadm, hiso⟩
  have hM : 0 < 1 / compactHeightScale p :=
    one_div_pos.mpr (compactHeightScale_pos p)
  unfold decodeOpenKink
  rw [rawOpenParam_compactOpenProfile p hadm
    (mass_eq_one_of_isIsotropic hiso)]
  exact ProfileDecode.normalizeParam_affine_of_isotropic hpfam _ _ hM

/-! ## Exact raw inverse: whole-line chart -/

def wholeLineKinkHeight (p : LogConcaveFamily6.WholeLineParam) : ℝ :=
  exp (p.c + p.beta * p.m)

lemma wholeLineOpenProfile_leftSlope
    (p : LogConcaveFamily6.WholeLineParam)
    (hadm : 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0)
    (hmass : wholeLineLeftMass p + wholeLineRightMass p = 1) :
    openLeftSlope (wholeLineOpenProfile p hadm hmass) =
      p.beta / wholeLineKinkHeight p := by
  have hm := wholeLine_left_mass_formula p hadm.2.1
  have ht := (wholeLine_left_mass_pos p hadm.2.1).ne'
  change (1 - 0) / wholeLineLeftMass p =
    p.beta / exp (p.c + p.beta * p.m)
  rw [hm]
  field_simp [hadm.2.1.ne', (exp_pos _).ne']
  norm_num

lemma wholeLineOpenProfile_rightSlope
    (p : LogConcaveFamily6.WholeLineParam)
    (hadm : 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0)
    (hmass : wholeLineLeftMass p + wholeLineRightMass p = 1) :
    openRightSlope (wholeLineOpenProfile p hadm hmass) =
      (p.beta - p.delta) / wholeLineKinkHeight p := by
  have hm := wholeLine_right_mass_formula p hadm.2.2
  have hsum : 1 - wholeLineLeftMass p = wholeLineRightMass p := by linarith
  have hs := hadm.2.2.ne
  change (0 - 1) / (1 - wholeLineLeftMass p) =
    (p.beta - p.delta) / exp (p.c + p.beta * p.m)
  rw [hsum, hm]
  field_simp [hs, (exp_pos _).ne']
  ring

lemma wholeLineOpenProfile_log_height
    (p : LogConcaveFamily6.WholeLineParam)
    (hadm : 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0)
    (hmass : wholeLineLeftMass p + wholeLineRightMass p = 1) :
    log (wholeLineOpenProfile p hadm hmass).h =
      log (1 / wholeLineKinkHeight p) + p.c + p.beta * p.m := by
  change log 1 = log (1 / exp (p.c + p.beta * p.m)) +
    p.c + p.beta * p.m
  rw [Real.log_one, one_div, Real.log_inv, Real.log_exp]
  ring

theorem rawWholeLine_wholeLineOpenProfile
    (p : LogConcaveFamily6.WholeLineParam)
    (hadm : 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0)
    (hmass : wholeLineLeftMass p + wholeLineRightMass p = 1) :
    rawWholeLine (wholeLineOpenProfile p hadm hmass) =
      affineWholeLine p p.m (1 / wholeLineKinkHeight p) := by
  have hls := wholeLineOpenProfile_leftSlope p hadm hmass
  have hrs := wholeLineOpenProfile_rightSlope p hadm hmass
  have hlog := wholeLineOpenProfile_log_height p hadm hmass
  cases p with
  | mk c beta delta m =>
      change LogConcaveFamily6.WholeLineParam.mk _ _ _ _ =
        LogConcaveFamily6.WholeLineParam.mk _ _ _ _
      rw [LogConcaveFamily6.WholeLineParam.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact hlog
      · change openLeftSlope (wholeLineOpenProfile
            ⟨c, beta, delta, m⟩ hadm hmass) =
          beta * (1 / wholeLineKinkHeight ⟨c, beta, delta, m⟩)
        rw [hls]
        ring
      · change openLeftSlope (wholeLineOpenProfile
            ⟨c, beta, delta, m⟩ hadm hmass) -
            openRightSlope (wholeLineOpenProfile
              ⟨c, beta, delta, m⟩ hadm hmass) =
          delta * (1 / wholeLineKinkHeight ⟨c, beta, delta, m⟩)
        rw [hls, hrs]
        ring
      · change 0 = (m - m) / (1 / wholeLineKinkHeight
          ⟨c, beta, delta, m⟩)
        ring

theorem rawOpenParam_wholeLineOpenProfile
    (p : LogConcaveFamily6.WholeLineParam)
    (hadm : 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0)
    (hmass : wholeLineLeftMass p + wholeLineRightMass p = 1) :
    rawOpenParam (wholeLineOpenProfile p hadm hmass) =
      affineParam (.wholeLine p) p.m (1 / wholeLineKinkHeight p) := by
  let u := wholeLineOpenProfile p hadm hmass
  have hl : u.l = 0 := rfl
  have hr : u.r = 0 := rfl
  change rawOpenParam u = _
  rw [rawOpenParam, dif_pos hl, dif_pos hr]
  change LogConcaveFamily6.Param.wholeLine _ =
    LogConcaveFamily6.Param.wholeLine _
  congr 1
  exact rawWholeLine_wholeLineOpenProfile p hadm hmass

theorem decodeOpenKink_wholeLineOpenProfile
    (p : LogConcaveFamily6.WholeLineParam)
    (hadm : 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0)
    (hiso : LogConcaveFamily6.IsIsotropic (.wholeLine p)) :
    let hmass : wholeLineLeftMass p + wholeLineRightMass p = 1 := by
      simpa [LogConcaveFamily6.integral, wholeLineLeftMass,
        wholeLineRightMass] using mass_eq_one_of_isIsotropic hiso
    decodeOpenKink (wholeLineOpenProfile p hadm hmass) = .wholeLine p := by
  dsimp only
  have hmass : wholeLineLeftMass p + wholeLineRightMass p = 1 := by
    simpa [LogConcaveFamily6.integral, wholeLineLeftMass,
      wholeLineRightMass] using mass_eq_one_of_isIsotropic hiso
  let hp : LogConcaveFamily6.Param := .wholeLine p
  have hpfam : hp ∈ LogConcaveFamily6.family6 := ⟨hadm, hiso⟩
  have hscale : 0 < 1 / wholeLineKinkHeight p := by
    exact one_div_pos.mpr (exp_pos _)
  unfold decodeOpenKink
  rw [rawOpenParam_wholeLineOpenProfile p hadm hmass]
  exact ProfileDecode.normalizeParam_affine_of_isotropic hpfam _ _ hscale

end LogConcaveFamily6.ProfileEncode

end FlattenedExistenceSection8


/-!
Flattened source section: ProfileEncodeFiniteLeft.lean
-/

section FlattenedExistenceSection9

open Real Set MeasureTheory intervalIntegral
open scoped Interval

namespace LogConcaveFamily6.ProfileEncode

open LogConcaveClaimI
open LogConcaveFamily6.ProfileDecode

/-! ## Exact raw inverse: finite-left chart -/

lemma finiteLeftOpenProfile_leftSlope
    (p : HalfLineParam)
    (hadm : p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0)
    (hmass : halfLineIntegral (fun _ : ℝ ↦ 1) p = 1) :
    openLeftSlope (finiteLeftOpenProfile p hadm hmass) =
      p 2 / finiteLeftHeightScale p := by
  have hd := finiteLeft_left_height_difference p
  have ht := (finiteLeft_left_mass_pos hadm.1).ne'
  change ((finiteLeftKinkHeight p / finiteLeftHeightScale p -
      finiteLeftLeftHeight p / finiteLeftHeightScale p) /
        finiteLeftKinkMass p) = p 2 / finiteLeftHeightScale p
  unfold finiteLeftKinkHeight finiteLeftLeftHeight finiteLeftKinkMass at ⊢
  field_simp [ht, (finiteLeftHeightScale_pos p).ne']
  nlinarith

lemma finiteLeftOpenProfile_rightSlope
    (p : HalfLineParam)
    (hadm : p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0)
    (hmass : halfLineIntegral (fun _ : ℝ ↦ 1) p = 1) :
    openRightSlope (finiteLeftOpenProfile p hadm hmass) =
      (p 2 - p 3) / finiteLeftHeightScale p := by
  have hd := finiteLeft_right_height_difference hadm.2.2
  have hsum : 1 - halfLineLeftIntegral (fun _ : ℝ ↦ 1) p =
      halfLineRightIntegral (fun _ : ℝ ↦ 1) p := by
    unfold halfLineIntegral at hmass
    linarith
  have hkink : halfLineRightExponent p (p 4) =
      halfLineLeftExponent p (p 4) := by
    simp [halfLineRightExponent, halfLineLeftExponent]
  rw [hkink] at hd
  change ((0 - finiteLeftKinkHeight p / finiteLeftHeightScale p) /
      (1 - finiteLeftKinkMass p)) =
        (p 2 - p 3) / finiteLeftHeightScale p
  unfold finiteLeftKinkHeight finiteLeftKinkMass at ⊢
  rw [hsum]
  field_simp [(finiteLeft_right_mass_pos hadm.2.2).ne',
    (finiteLeftHeightScale_pos p).ne']
  nlinarith

lemma finiteLeft_left_mass_of_zero_slope
    (p : HalfLineParam) (hbeta : p 2 = 0) :
    halfLineLeftIntegral (fun _ : ℝ ↦ 1) p =
      exp (halfLineLeftExponent p (p 0)) * (p 4 - p 0) := by
  unfold halfLineLeftIntegral halfLineLeftIntegrand halfLineLeftExponent
  simp [hbeta]
  ring

lemma finiteLeftOpenProfile_leftLength
    (p : HalfLineParam)
    (hadm : p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0)
    (hmass : halfLineIntegral (fun _ : ℝ ↦ 1) p = 1) :
    openLeftLength (finiteLeftOpenProfile p hadm hmass) =
      finiteLeftHeightScale p * (p 4 - p 0) := by
  let u := finiteLeftOpenProfile p hadm hmass
  have hM := finiteLeftHeightScale_pos p
  have hsl := finiteLeftOpenProfile_leftSlope p hadm hmass
  unfold openLeftLength
  by_cases hbeta : p 2 = 0
  · have hs : openLeftSlope u = 0 := by rw [hsl, hbeta, zero_div]
    rw [if_pos hs]
    have hm := finiteLeft_left_mass_of_zero_slope p hbeta
    change finiteLeftKinkMass p /
        (finiteLeftLeftHeight p / finiteLeftHeightScale p) = _
    unfold finiteLeftKinkMass finiteLeftLeftHeight
    rw [hm]
    field_simp [hM.ne']
  · have hs : openLeftSlope u ≠ 0 := by
      rw [hsl]
      exact div_ne_zero hbeta hM.ne'
    rw [if_neg hs, hsl]
    change log ((finiteLeftKinkHeight p / finiteLeftHeightScale p) /
        (finiteLeftLeftHeight p / finiteLeftHeightScale p)) /
          (p 2 / finiteLeftHeightScale p) = _
    have hratio :
        (finiteLeftKinkHeight p / finiteLeftHeightScale p) /
            (finiteLeftLeftHeight p / finiteLeftHeightScale p) =
          exp (p 2 * (p 4 - p 0)) := by
      unfold finiteLeftKinkHeight finiteLeftLeftHeight halfLineLeftExponent
      calc
        exp (p 1 + p 2 * p 4) / finiteLeftHeightScale p /
            (exp (p 1 + p 2 * p 0) / finiteLeftHeightScale p) =
          exp (p 1 + p 2 * p 4) / exp (p 1 + p 2 * p 0) := by
            field_simp [hM.ne', (exp_pos (p 1 + p 2 * p 0)).ne']
        _ = exp ((p 1 + p 2 * p 4) - (p 1 + p 2 * p 0)) := by
          rw [Real.exp_sub]
        _ = exp (p 2 * (p 4 - p 0)) := by congr 1 <;> ring
    rw [hratio, Real.log_exp]
    field_simp [hbeta, hM.ne']

lemma finiteLeftOpenProfile_log_left
    (p : HalfLineParam)
    (hadm : p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0)
    (hmass : halfLineIntegral (fun _ : ℝ ↦ 1) p = 1) :
    log (finiteLeftOpenProfile p hadm hmass).l =
      log (1 / finiteLeftHeightScale p) + p 1 + p 2 * p 0 := by
  have hM := finiteLeftHeightScale_pos p
  change log (exp (halfLineLeftExponent p (p 0)) /
      finiteLeftHeightScale p) = _
  rw [Real.log_div (exp_pos _).ne' hM.ne', Real.log_exp]
  have hinv : log (1 / finiteLeftHeightScale p) =
      -log (finiteLeftHeightScale p) := by
    rw [one_div, Real.log_inv]
  rw [hinv]
  unfold halfLineLeftExponent
  ring

theorem rawFiniteLeft_finiteLeftOpenProfile
    (p : HalfLineParam)
    (hadm : p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0)
    (hmass : halfLineIntegral (fun _ : ℝ ↦ 1) p = 1) :
    rawFiniteLeft (finiteLeftOpenProfile p hadm hmass) =
      affineHalfLine p (p 0) (1 / finiteLeftHeightScale p) := by
  let u := finiteLeftOpenProfile p hadm hmass
  have hleftSlope := finiteLeftOpenProfile_leftSlope p hadm hmass
  have hrightSlope := finiteLeftOpenProfile_rightSlope p hadm hmass
  have hleftLength := finiteLeftOpenProfile_leftLength p hadm hmass
  have hlog := finiteLeftOpenProfile_log_left p hadm hmass
  funext i
  fin_cases i
  · simp [rawFiniteLeft, affineHalfLine]
  · simpa [rawFiniteLeft, affineHalfLine] using hlog
  · change openLeftSlope u = p 2 * (1 / finiteLeftHeightScale p)
    rw [hleftSlope]
    ring
  · change openLeftSlope u - openRightSlope u =
      p 3 * (1 / finiteLeftHeightScale p)
    rw [hleftSlope, hrightSlope]
    ring
  · change openLeftLength u = (p 4 - p 0) / (1 / finiteLeftHeightScale p)
    rw [hleftLength]
    field_simp [(finiteLeftHeightScale_pos p).ne']

theorem rawOpenParam_finiteLeftOpenProfile
    (p : HalfLineParam)
    (hadm : p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0)
    (hmass : halfLineIntegral (fun _ : ℝ ↦ 1) p = 1) :
    rawOpenParam (finiteLeftOpenProfile p hadm hmass) =
      affineParam (.finiteLeft p) (p 0) (1 / finiteLeftHeightScale p) := by
  let u := finiteLeftOpenProfile p hadm hmass
  have hl : u.l ≠ 0 :=
    (div_pos (exp_pos _) (finiteLeftHeightScale_pos p)).ne'
  have hr : u.r = 0 := rfl
  change rawOpenParam u = _
  rw [rawOpenParam, dif_neg hl, dif_pos hr]
  change LogConcaveFamily6.Param.finiteLeft _ =
    LogConcaveFamily6.Param.finiteLeft _
  congr 1
  exact rawFiniteLeft_finiteLeftOpenProfile p hadm hmass

theorem decodeOpenKink_finiteLeftOpenProfile
    (p : HalfLineParam)
    (hadm : p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0)
    (hiso : LogConcaveFamily6.IsIsotropic (.finiteLeft p)) :
    decodeOpenKink
        (finiteLeftOpenProfile p hadm (mass_eq_one_of_isIsotropic hiso)) =
      .finiteLeft p := by
  let hp : LogConcaveFamily6.Param := .finiteLeft p
  have hpfam : hp ∈ LogConcaveFamily6.family6 := ⟨hadm, hiso⟩
  have hM : 0 < 1 / finiteLeftHeightScale p :=
    one_div_pos.mpr (finiteLeftHeightScale_pos p)
  unfold decodeOpenKink
  rw [rawOpenParam_finiteLeftOpenProfile p hadm
    (mass_eq_one_of_isIsotropic hiso)]
  exact normalizeParam_affine_of_isotropic hpfam _ _ hM

end LogConcaveFamily6.ProfileEncode

end FlattenedExistenceSection9


/-!
Flattened source section: ProfileEncodeFiniteRight.lean
-/

section FlattenedExistenceSection10

open Real Set MeasureTheory intervalIntegral
open scoped Interval

namespace LogConcaveFamily6.ProfileEncode

open LogConcaveClaimI
open LogConcaveFamily6.ProfileDecode

/-! ## Exact raw inverse: finite-right chart -/

lemma finiteRightOpenProfile_leftSlope
    (p : HalfLineParam)
    (hadm : p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2)
    (hmass : finiteRightActualIntegral (fun _ : ℝ ↦ 1) p = 1) :
    openLeftSlope (finiteRightOpenProfile p hadm hmass) =
      p 2 / finiteRightHeightScale p := by
  have hd := finiteRight_left_height_difference hadm.2.2
  have ht := (finiteRight_left_mass_pos hadm.2.2).ne'
  change ((finiteRightKinkHeight p / finiteRightHeightScale p - 0) /
      finiteRightKinkMass p) = p 2 / finiteRightHeightScale p
  unfold finiteRightKinkHeight finiteRightKinkMass at ⊢
  field_simp [ht, (finiteRightHeightScale_pos p).ne']
  nlinarith

lemma finiteRightOpenProfile_rightSlope
    (p : HalfLineParam)
    (hadm : p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2)
    (hmass : finiteRightActualIntegral (fun _ : ℝ ↦ 1) p = 1) :
    openRightSlope (finiteRightOpenProfile p hadm hmass) =
      (p 2 - p 3) / finiteRightHeightScale p := by
  have hd := finiteRight_right_height_difference p
  have hsum : 1 - finiteRightLeftTailIntegral (fun _ : ℝ ↦ 1) p =
      finiteRightRightCompactIntegral (fun _ : ℝ ↦ 1) p := by
    unfold finiteRightActualIntegral at hmass
    linarith
  have hkink : finiteRightRightExponent p (p 4) =
      finiteRightLeftExponent p (p 4) := by
    simp [finiteRightRightExponent, finiteRightLeftExponent]
  rw [hkink] at hd
  change ((finiteRightRightHeight p / finiteRightHeightScale p -
      finiteRightKinkHeight p / finiteRightHeightScale p) /
        (1 - finiteRightKinkMass p)) =
      (p 2 - p 3) / finiteRightHeightScale p
  unfold finiteRightRightHeight finiteRightKinkHeight finiteRightKinkMass at ⊢
  rw [hsum]
  field_simp [(finiteRight_right_mass_pos hadm.1).ne',
    (finiteRightHeightScale_pos p).ne']
  nlinarith

lemma finiteRight_right_mass_of_zero_slope
    (p : HalfLineParam) (hslope : p 2 - p 3 = 0) :
    finiteRightRightCompactIntegral (fun _ : ℝ ↦ 1) p =
      exp (finiteRightRightExponent p (p 4)) * (p 0 - p 4) := by
  unfold finiteRightRightCompactIntegral finiteRightRightIntegrand
  simp only [one_mul]
  have hconst : ∀ x : ℝ,
      finiteRightRightExponent p x = finiteRightRightExponent p (p 4) := by
    intro x
    have heq : p 2 = p 3 := by linarith
    unfold finiteRightRightExponent
    rw [heq]
    ring
  calc
    (∫ x in p 4..p 0, exp (finiteRightRightExponent p x)) =
        ∫ _x in p 4..p 0, exp (finiteRightRightExponent p (p 4)) := by
          apply intervalIntegral.integral_congr
          intro x _
          change exp (finiteRightRightExponent p x) =
            exp (finiteRightRightExponent p (p 4))
          rw [hconst x]
    _ = _ := by simp; ring

lemma finiteRightOpenProfile_rightLength
    (p : HalfLineParam)
    (hadm : p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2)
    (hmass : finiteRightActualIntegral (fun _ : ℝ ↦ 1) p = 1) :
    openRightLength (finiteRightOpenProfile p hadm hmass) =
      finiteRightHeightScale p * (p 0 - p 4) := by
  let u := finiteRightOpenProfile p hadm hmass
  have hM := finiteRightHeightScale_pos p
  have hsr := finiteRightOpenProfile_rightSlope p hadm hmass
  unfold openRightLength
  by_cases hslope : p 2 - p 3 = 0
  · have hs : openRightSlope u = 0 := by rw [hsr, hslope, zero_div]
    rw [if_pos hs]
    have hm := finiteRight_right_mass_of_zero_slope p hslope
    have hsum : 1 - finiteRightKinkMass p =
        finiteRightRightCompactIntegral (fun _ : ℝ ↦ 1) p := by
      unfold finiteRightKinkMass
      unfold finiteRightActualIntegral at hmass
      linarith
    change (1 - finiteRightKinkMass p) /
        (finiteRightKinkHeight p / finiteRightHeightScale p) = _
    rw [hsum, hm]
    have hkink : finiteRightRightExponent p (p 4) =
        finiteRightLeftExponent p (p 4) := by
      simp [finiteRightRightExponent, finiteRightLeftExponent]
    unfold finiteRightKinkHeight
    rw [hkink]
    field_simp [hM.ne']
  · have hs : openRightSlope u ≠ 0 := by
      rw [hsr]
      exact div_ne_zero hslope hM.ne'
    rw [if_neg hs, hsr]
    change log ((finiteRightRightHeight p / finiteRightHeightScale p) /
        (finiteRightKinkHeight p / finiteRightHeightScale p)) /
          ((p 2 - p 3) / finiteRightHeightScale p) = _
    have hratio :
        (finiteRightRightHeight p / finiteRightHeightScale p) /
            (finiteRightKinkHeight p / finiteRightHeightScale p) =
          exp ((p 2 - p 3) * (p 0 - p 4)) := by
      unfold finiteRightRightHeight finiteRightKinkHeight
      unfold finiteRightRightExponent finiteRightLeftExponent
      calc
        exp (p 1 + p 2 * p 0 - p 3 * (p 0 - p 4)) /
              finiteRightHeightScale p /
            (exp (p 1 + p 2 * p 4) / finiteRightHeightScale p) =
          exp (p 1 + p 2 * p 0 - p 3 * (p 0 - p 4)) /
            exp (p 1 + p 2 * p 4) := by
              field_simp [hM.ne', (exp_pos (p 1 + p 2 * p 4)).ne']
        _ = exp ((p 1 + p 2 * p 0 - p 3 * (p 0 - p 4)) -
            (p 1 + p 2 * p 4)) := by
              exact (Real.exp_sub _ _).symm
        _ = exp ((p 2 - p 3) * (p 0 - p 4)) := by congr 1 <;> ring
    rw [hratio, Real.log_exp]
    field_simp [hslope, hM.ne']

lemma finiteRightOpenProfile_log_kink
    (p : HalfLineParam)
    (hadm : p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2)
    (hmass : finiteRightActualIntegral (fun _ : ℝ ↦ 1) p = 1) :
    log (finiteRightOpenProfile p hadm hmass).h =
      log (1 / finiteRightHeightScale p) + p 1 + p 2 * p 4 := by
  have hM := finiteRightHeightScale_pos p
  change log (exp (finiteRightLeftExponent p (p 4)) /
      finiteRightHeightScale p) = _
  rw [Real.log_div (exp_pos _).ne' hM.ne', Real.log_exp]
  have hinv : log (1 / finiteRightHeightScale p) =
      -log (finiteRightHeightScale p) := by
    rw [one_div, Real.log_inv]
  rw [hinv]
  unfold finiteRightLeftExponent
  ring

theorem rawFiniteRight_finiteRightOpenProfile
    (p : HalfLineParam)
    (hadm : p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2)
    (hmass : finiteRightActualIntegral (fun _ : ℝ ↦ 1) p = 1) :
    rawFiniteRight (finiteRightOpenProfile p hadm hmass) =
      affineHalfLine p (p 4) (1 / finiteRightHeightScale p) := by
  let u := finiteRightOpenProfile p hadm hmass
  have hleftSlope := finiteRightOpenProfile_leftSlope p hadm hmass
  have hrightSlope := finiteRightOpenProfile_rightSlope p hadm hmass
  have hrightLength := finiteRightOpenProfile_rightLength p hadm hmass
  have hlog := finiteRightOpenProfile_log_kink p hadm hmass
  funext i
  fin_cases i
  · change openRightLength u = (p 0 - p 4) / (1 / finiteRightHeightScale p)
    rw [hrightLength]
    field_simp [(finiteRightHeightScale_pos p).ne']
  · simpa [rawFiniteRight, affineHalfLine] using hlog
  · change openLeftSlope u = p 2 * (1 / finiteRightHeightScale p)
    rw [hleftSlope]
    ring
  · change openLeftSlope u - openRightSlope u =
      p 3 * (1 / finiteRightHeightScale p)
    rw [hleftSlope, hrightSlope]
    ring
  · simp [rawFiniteRight, affineHalfLine]

theorem rawOpenParam_finiteRightOpenProfile
    (p : HalfLineParam)
    (hadm : p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2)
    (hmass : finiteRightActualIntegral (fun _ : ℝ ↦ 1) p = 1) :
    rawOpenParam (finiteRightOpenProfile p hadm hmass) =
      affineParam (.finiteRight p) (p 4) (1 / finiteRightHeightScale p) := by
  let u := finiteRightOpenProfile p hadm hmass
  have hl : u.l = 0 := rfl
  have hr : u.r ≠ 0 :=
    (div_pos (exp_pos _) (finiteRightHeightScale_pos p)).ne'
  change rawOpenParam u = _
  rw [rawOpenParam, dif_pos hl, dif_neg hr]
  change LogConcaveFamily6.Param.finiteRight _ =
    LogConcaveFamily6.Param.finiteRight _
  congr 1
  exact rawFiniteRight_finiteRightOpenProfile p hadm hmass

theorem decodeOpenKink_finiteRightOpenProfile
    (p : HalfLineParam)
    (hadm : p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2)
    (hiso : LogConcaveFamily6.IsIsotropic (.finiteRight p)) :
    decodeOpenKink
        (finiteRightOpenProfile p hadm (mass_eq_one_of_isIsotropic hiso)) =
      .finiteRight p := by
  let hp : LogConcaveFamily6.Param := .finiteRight p
  have hpfam : hp ∈ LogConcaveFamily6.family6 := ⟨hadm, hiso⟩
  have hM : 0 < 1 / finiteRightHeightScale p :=
    one_div_pos.mpr (finiteRightHeightScale_pos p)
  unfold decodeOpenKink
  rw [rawOpenParam_finiteRightOpenProfile p hadm
    (mass_eq_one_of_isIsotropic hiso)]
  exact normalizeParam_affine_of_isotropic hpfam _ _ hM

end LogConcaveFamily6.ProfileEncode

end FlattenedExistenceSection10


/-!
Flattened source section: ProfileEncodeCoverage.lean
-/

section FlattenedExistenceSection11

namespace LogConcaveFamily6.ProfileEncode

open LogConcaveFamily6.ProfileDecode

/-- All-tag exact recovery, with the finite-right chart isolated as the only
input while that symmetric chart is developed in a separate module. -/
theorem decodeOpenKink_encodeOpenProfile_of_finiteRight
    (hfiniteRight : ∀ (p : LogConcaveClaimI.HalfLineParam)
      (hadm : p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2)
      (hiso : LogConcaveFamily6.IsIsotropic (.finiteRight p)),
      decodeOpenKink
          (finiteRightOpenProfile p hadm (mass_eq_one_of_isIsotropic hiso)) =
        .finiteRight p)
    (q : LogConcaveFamily6.Param) (hq : q ∈ LogConcaveFamily6.family6) :
    decodeOpenKink (encodeOpenProfile q hq) = q := by
  rcases hq with ⟨hadm, hiso⟩
  cases q with
  | compact p =>
      exact decodeOpenKink_compactOpenProfile p hadm hiso
  | finiteLeft p =>
      exact decodeOpenKink_finiteLeftOpenProfile p hadm hiso
  | finiteRight p =>
      exact hfiniteRight p hadm hiso
  | wholeLine p =>
      exact decodeOpenKink_wholeLineOpenProfile p hadm hiso

/-- Encoding a tagged isotropic member of family (6), reconstructing the
raw profile, and standardizing it recovers the original parameter exactly. -/
theorem decodeOpenKink_encodeOpenProfile
    (q : LogConcaveFamily6.Param) (hq : q ∈ LogConcaveFamily6.family6) :
    decodeOpenKink (encodeOpenProfile q hq) = q := by
  exact decodeOpenKink_encodeOpenProfile_of_finiteRight
    decodeOpenKink_finiteRightOpenProfile q hq

end LogConcaveFamily6.ProfileEncode

end FlattenedExistenceSection11


/-!
Flattened source section: ProfileDecodeAll.lean
-/

section FlattenedExistenceSection12

/-!
# Decoding every normalized profile

This file removes the collapsed cases `p = 0,1` and packages every point of
the compact normalized profile space as an `OpenKinkProfile`, the unified
input type of the explicit compact/half-line/whole-line decoder.
-/



open Real Set

namespace LogConcaveFamily6.ProfileCompactification

open LogConcaveFamily6.ProfileDecode
open LogConcaveFamily6.ProfileEncode

/-- The genuine-open-kink profile obtained after harmless endpoint
interiorization. -/
def normalizedOpenProfile (u : ProfileParam) (hu : u ∈ normalizedProfiles) :
    OpenKinkProfile where
  p := kinkMass (interiorizeKinkMass u)
  l := leftValue (interiorizeKinkMass u)
  h := kinkValue (interiorizeKinkMass u)
  r := rightValue (interiorizeKinkMass u)
  p_pos := kinkMass_interiorizeKinkMass_pos hu
  p_lt_one := kinkMass_interiorizeKinkMass_lt_one hu
  l_nonneg := leftValue_nonneg (interiorizeKinkMass_mem hu)
  h_pos := by
    let v := interiorizeKinkMass u
    have hv : v ∈ normalizedProfiles := interiorizeKinkMass_mem hu
    have hp0 : 0 < kinkMass v := kinkMass_interiorizeKinkMass_pos hu
    have hp1 : kinkMass v < 1 := kinkMass_interiorizeKinkMass_lt_one hu
    have hc := profile_concavity hv
    rcases one_profile_coordinate_eq_one hv with hl | hh | hr
    · have : 0 < (1 - kinkMass v) * leftValue v :=
        mul_pos (sub_pos.mpr hp1) (by rw [hl]; norm_num)
      nlinarith [mul_nonneg hp0.le (rightValue_nonneg hv)]
    · change 0 < kinkValue v
      rw [hh]
      norm_num
    · have : 0 < kinkMass v * rightValue v :=
        mul_pos hp0 (by rw [hr]; norm_num)
      nlinarith [mul_nonneg (sub_nonneg.mpr hp1.le) (leftValue_nonneg hv)]
  r_nonneg := rightValue_nonneg (interiorizeKinkMass_mem hu)
  concave := profile_concavity (interiorizeKinkMass_mem hu)

@[simp] theorem normalizedOpenProfile_p (u : ProfileParam)
    (hu : u ∈ normalizedProfiles) :
    (normalizedOpenProfile u hu).p = kinkMass (interiorizeKinkMass u) := rfl

@[simp] theorem normalizedOpenProfile_l (u : ProfileParam)
    (hu : u ∈ normalizedProfiles) :
    (normalizedOpenProfile u hu).l = leftValue (interiorizeKinkMass u) := rfl

@[simp] theorem normalizedOpenProfile_h (u : ProfileParam)
    (hu : u ∈ normalizedProfiles) :
    (normalizedOpenProfile u hu).h = kinkValue (interiorizeKinkMass u) := rfl

@[simp] theorem normalizedOpenProfile_r (u : ProfileParam)
    (hu : u ∈ normalizedProfiles) :
    (normalizedOpenProfile u hu).r = rightValue (interiorizeKinkMass u) := rfl

/-- Forgetting the proof fields recovers exactly the interiorized profile. -/
theorem openProfileParam_normalizedOpenProfile (u : ProfileParam)
    (hu : u ∈ normalizedProfiles) :
    openProfileParam (normalizedOpenProfile u hu) = interiorizeKinkMass u := by
  funext i
  fin_cases i <;> rfl

/-- The explicit family-(6) parameter decoded from a normalized profile. -/
def decodeNormalizedProfile (u : ProfileParam)
    (hu : u ∈ normalizedProfiles) : LogConcaveFamily6.Param :=
  decodeOpenKink (normalizedOpenProfile u hu)

theorem decodeNormalizedProfile_mem_family6 (u : ProfileParam)
    (hu : u ∈ normalizedProfiles) :
    decodeNormalizedProfile u hu ∈ LogConcaveFamily6.family6 :=
  decodeOpenKink_mem_family6 (normalizedOpenProfile u hu)

end LogConcaveFamily6.ProfileCompactification

end FlattenedExistenceSection12


/-!
Flattened source section: ProfileTailSubstitution.lean
-/

section FlattenedExistenceSection13

/-!
# Exponential-tail substitutions for quantile-density profiles

These two lemmas are the improper endpoint cases of the quantile
substitution.  They are stated for an arbitrary real-valued integrand; the
one-dimensional Jacobian theorem therefore also covers the non-integrable
case under Lean's convention for the Bochner integral.
-/



open Real Set MeasureTheory intervalIntegral
open scoped Interval

namespace LogConcaveFamily6.ProfileTailSubstitution

/-- On a left exponential tail, `t = p exp(s x)` sends `(-∞,0]` to
`(0,p]` and its Jacobian is `h exp(s x)` when `h = s p`. -/
theorem integral_Iic_exp_to_interval
    (q : ℝ → ℝ) {s h p : ℝ}
    (hs : 0 < s) (hp : 0 < p) (hh : h = s * p) :
    (∫ x : ℝ in Iic 0, q x * (h * exp (s * x))) =
      ∫ t in (0 : ℝ)..p, q (log (t / p) / s) := by
  let f : ℝ → ℝ := fun x ↦ p * exp (s * x)
  let f' : ℝ → ℝ := fun x ↦ p * s * exp (s * x)
  let g : ℝ → ℝ := fun t ↦ q (log (t / p) / s)
  have hderiv : ∀ x ∈ Iic (0 : ℝ),
      HasDerivWithinAt f (f' x) (Iic 0) x := by
    intro x _
    have he : HasDerivAt (fun y : ℝ ↦ exp (s * y))
        (s * exp (s * x)) x := by
      simpa only [Function.comp_def, one_mul, mul_one, mul_comm] using
        (Real.hasDerivAt_exp (s * x)).comp x
        ((hasDerivAt_id x).const_mul s)
    simpa [f, f', mul_assoc] using (he.const_mul p).hasDerivWithinAt
  have hinj : InjOn f (Iic (0 : ℝ)) := by
    intro x _ y _ hxy
    have hexp : exp (s * x) = exp (s * y) := by
      apply (mul_left_cancel₀ hp.ne')
      exact hxy
    have harg : s * x = s * y := Real.exp_injective hexp
    nlinarith
  have himage : f '' Iic (0 : ℝ) = Ioc 0 p := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor
      · exact mul_pos hp (exp_pos _)
      · have hsx : s * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le hx
        have he : exp (s * x) ≤ 1 := by simpa using Real.exp_le_one_iff.mpr hsx
        nlinarith [mul_nonneg hp.le (sub_nonneg.mpr he)]
    · intro ht
      let x : ℝ := log (t / p) / s
      have hratio : 0 < t / p := div_pos ht.1 hp
      have hratio_le : t / p ≤ 1 := (div_le_one hp).2 ht.2
      have hx : x ∈ Iic (0 : ℝ) := by
        change log (t / p) / s ≤ 0
        exact div_nonpos_of_nonpos_of_nonneg
          (Real.log_nonpos hratio.le hratio_le) hs.le
      refine ⟨x, hx, ?_⟩
      change p * exp (s * (log (t / p) / s)) = t
      have hs0 := hs.ne'
      rw [show s * (log (t / p) / s) = log (t / p) by field_simp [hs0],
        Real.exp_log hratio]
      field_simp [hp.ne']
  have hcv := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Iic hderiv hinj g
  rw [himage] at hcv
  have habs : ∀ x : ℝ, |f' x| = h * exp (s * x) := by
    intro x
    rw [hh]
    have hps : 0 ≤ p * s := mul_nonneg hp.le hs.le
    simp only [f', abs_mul, abs_of_nonneg hps, abs_of_pos (exp_pos _)]
    ring
  rw [intervalIntegral.integral_of_le hp.le]
  rw [hcv]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
  intro x hx
  change q x * (h * exp (s * x)) = |f' x| • g (f x)
  rw [habs x]
  change q x * (h * exp (s * x)) =
    (h * exp (s * x)) * q (log ((p * exp (s * x)) / p) / s)
  have hratio : (p * exp (s * x)) / p = exp (s * x) := by
    field_simp [hp.ne']
  rw [hratio, Real.log_exp]
  have hs0 := hs.ne'
  have hxdiv : s * x / s = x := by field_simp [hs0]
  rw [hxdiv]
  ring

/-- On a right exponential tail, `t = 1-(1-p) exp(s x)` sends `[0,∞)`
to `[p,1)` and its Jacobian is `h exp(s x)` when
`h = -s(1-p)`.  Removing either endpoint does not change the integrals. -/
theorem integral_Ioi_exp_to_interval
    (q : ℝ → ℝ) {s h p : ℝ}
    (hs : s < 0) (hp : p < 1) (hh : h = -s * (1 - p)) :
    (∫ x : ℝ in Ioi 0, q x * (h * exp (s * x))) =
      ∫ t in p..(1 : ℝ), q (log ((1 - t) / (1 - p)) / s) := by
  let f : ℝ → ℝ := fun x ↦ 1 - (1 - p) * exp (s * x)
  let f' : ℝ → ℝ := fun x ↦ -(1 - p) * s * exp (s * x)
  let g : ℝ → ℝ := fun t ↦ q (log ((1 - t) / (1 - p)) / s)
  have ha : 0 < 1 - p := sub_pos.mpr hp
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivWithinAt f (f' x) (Ici 0) x := by
    intro x _
    have he : HasDerivAt (fun y : ℝ ↦ exp (s * y))
        (s * exp (s * x)) x := by
      simpa only [Function.comp_def, one_mul, mul_one, mul_comm] using
        (Real.hasDerivAt_exp (s * x)).comp x
          ((hasDerivAt_id x).const_mul s)
    have hc : HasDerivAt (fun _y : ℝ ↦ (1 : ℝ)) 0 x :=
      hasDerivAt_const x 1
    have hm := hc.sub (he.const_mul (1 - p))
    change HasDerivWithinAt
      (fun y : ℝ ↦ 1 - (1 - p) * exp (s * y))
      (-(1 - p) * s * exp (s * x)) (Ici 0) x
    exact (hm.congr_deriv (by ring)).hasDerivWithinAt
  have hinj : InjOn f (Ici (0 : ℝ)) := by
    intro x _ y _ hxy
    have hmul : (1 - p) * exp (s * x) = (1 - p) * exp (s * y) := by
      linarith
    have hexp : exp (s * x) = exp (s * y) := by
      apply (mul_left_cancel₀ ha.ne')
      exact hmul
    have harg : s * x = s * y := Real.exp_injective hexp
    nlinarith
  have himage : f '' Ici (0 : ℝ) = Ico p 1 := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor
      · have hsx : s * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs.le hx
        have he : exp (s * x) ≤ 1 := by simpa using Real.exp_le_one_iff.mpr hsx
        nlinarith [mul_nonneg ha.le (sub_nonneg.mpr he)]
      · nlinarith [mul_pos ha (exp_pos (s * x))]
    · intro ht
      let x : ℝ := log ((1 - t) / (1 - p)) / s
      have hratio : 0 < (1 - t) / (1 - p) :=
        div_pos (sub_pos.mpr ht.2) ha
      have hratio_le : (1 - t) / (1 - p) ≤ 1 := by
        exact (div_le_one ha).2 (by linarith [ht.1])
      have hx : x ∈ Ici (0 : ℝ) := by
        change 0 ≤ log ((1 - t) / (1 - p)) / s
        exact div_nonneg_of_nonpos
          (Real.log_nonpos hratio.le hratio_le) hs.le
      refine ⟨x, hx, ?_⟩
      change 1 - (1 - p) *
        exp (s * (log ((1 - t) / (1 - p)) / s)) = t
      have hs0 := hs.ne
      have hcancel : s * (log ((1 - t) / (1 - p)) / s) =
          log ((1 - t) / (1 - p)) := by field_simp [hs0]
      rw [hcancel, Real.exp_log hratio]
      field_simp [ha.ne']
      ring
  have hcv := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ici hderiv hinj g
  rw [himage] at hcv
  have habs : ∀ x : ℝ, |f' x| = h * exp (s * x) := by
    intro x
    rw [hh]
    have hcoef : 0 ≤ -(1 - p) * s :=
      mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr ha.le) hs.le
    simp only [f', abs_mul, abs_of_nonneg hcoef, abs_of_pos (exp_pos _)]
    ring
  rw [intervalIntegral.integral_of_le hp.le]
  rw [← MeasureTheory.integral_Ico_eq_integral_Ioc]
  rw [hcv]
  rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change q x * (h * exp (s * x)) = |f' x| • g (f x)
  rw [habs x]
  change q x * (h * exp (s * x)) =
    (h * exp (s * x)) *
      q (log ((1 - (1 - (1 - p) * exp (s * x))) / (1 - p)) / s)
  have hratio :
      (1 - (1 - (1 - p) * exp (s * x))) / (1 - p) = exp (s * x) := by
    field_simp [ha.ne']
    ring
  rw [hratio, Real.log_exp]
  have hs0 := hs.ne
  have hxdiv : s * x / s = x := by field_simp [hs0]
  rw [hxdiv]
  ring

/-- Shifted form of `integral_Iic_exp_to_interval`, with the kink at `m`. -/
theorem integral_Iic_exp_shift_to_interval
    (q : ℝ → ℝ) {s h p m : ℝ}
    (hs : 0 < s) (hp : 0 < p) (hh : h = s * p) :
    (∫ x : ℝ in Iic m, q x * (h * exp (s * (x - m)))) =
      ∫ t in (0 : ℝ)..p, q (m + log (t / p) / s) := by
  let F : ℝ → ℝ := fun x ↦ q x * (h * exp (s * (x - m)))
  have hshift := LogConcaveFamily6.ProfileDecode.integral_Iic_standardize
    F m m 1 (by norm_num : (0 : ℝ) < 1)
  have hbase := integral_Iic_exp_to_interval
    (fun y ↦ q (m + y)) hs hp hh
  calc
    (∫ x : ℝ in Iic m, q x * (h * exp (s * (x - m)))) =
        ∫ y : ℝ in Iic 0, q (m + y) * (h * exp (s * y)) := by
          simpa [F, add_comm] using hshift.symm
    _ = ∫ t in (0 : ℝ)..p, q (m + log (t / p) / s) := hbase

/-- Shifted form of `integral_Ioi_exp_to_interval`, with the kink at `m`. -/
theorem integral_Ioi_exp_shift_to_interval
    (q : ℝ → ℝ) {s h p m : ℝ}
    (hs : s < 0) (hp : p < 1) (hh : h = -s * (1 - p)) :
    (∫ x : ℝ in Ioi m, q x * (h * exp (s * (x - m)))) =
      ∫ t in p..(1 : ℝ), q (m + log ((1 - t) / (1 - p)) / s) := by
  let F : ℝ → ℝ := fun x ↦ q x * (h * exp (s * (x - m)))
  have hshift := LogConcaveFamily6.ProfileDecode.integral_Ioi_standardize
    F m m 1 (by norm_num : (0 : ℝ) < 1)
  have hbase := integral_Ioi_exp_to_interval
    (fun y ↦ q (m + y)) hs hp hh
  calc
    (∫ x : ℝ in Ioi m, q x * (h * exp (s * (x - m)))) =
        ∫ y : ℝ in Ioi 0, q (m + y) * (h * exp (s * y)) := by
          simpa [F, add_comm] using hshift.symm
    _ = ∫ t in p..(1 : ℝ),
        q (m + log ((1 - t) / (1 - p)) / s) := hbase

end LogConcaveFamily6.ProfileTailSubstitution

end FlattenedExistenceSection13


/-!
Flattened source section: ProfileTailDensity.lean
-/

section FlattenedExistenceSection14

/-!
# Pointwise tail densities for the raw profile decoder

These identities expose every unbounded piece reconstructed by
`rawFiniteRight`, `rawFiniteLeft`, and `rawWholeLine` as an exponential
anchored at its kink.  They are independent of integration and can therefore
be used directly in the tail change-of-variables argument.
-/



open Real

namespace LogConcaveFamily6.ProfileDecode

open LogConcaveClaimI

/-! ## Finite-right support: the kink is at zero -/

theorem rawFiniteRight_left_weight_eq (u : OpenKinkProfile) (x : ℝ) :
    exp (finiteRightLeftExponent (rawFiniteRight u) x) =
      u.h * exp (openLeftSlope u * x) := by
  simp only [finiteRightLeftExponent, rawFiniteRight_one, rawFiniteRight_two]
  rw [Real.exp_add, Real.exp_log u.h_pos]

theorem rawFiniteRight_right_weight_eq (u : OpenKinkProfile) (x : ℝ) :
    exp (finiteRightRightExponent (rawFiniteRight u) x) =
      u.h * exp (openRightSlope u * x) := by
  simp only [finiteRightRightExponent, rawFiniteRight_one, rawFiniteRight_two,
    rawFiniteRight_three, rawFiniteRight_four, sub_zero]
  rw [show log u.h + openLeftSlope u * x -
      (openLeftSlope u - openRightSlope u) * x =
        log u.h + openRightSlope u * x by ring,
    Real.exp_add, Real.exp_log u.h_pos]

/-! ## Finite-left support: the kink is at `openLeftLength u` -/

theorem rawFiniteLeft_left_weight_eq (u : OpenKinkProfile)
    (hl : 0 < u.l) (x : ℝ) :
    exp (halfLineLeftExponent (rawFiniteLeft u) x) =
      u.h * exp (openLeftSlope u * (x - openLeftLength u)) := by
  have hk := rawFiniteLeft_kink_value u hl
  simp only [halfLineLeftExponent, rawFiniteLeft_one,
    rawFiniteLeft_two] at hk ⊢
  rw [← hk, ← Real.exp_add]
  congr 1
  ring

theorem rawFiniteLeft_right_weight_eq (u : OpenKinkProfile)
    (hl : 0 < u.l) (x : ℝ) :
    exp (halfLineRightExponent (rawFiniteLeft u) x) =
      u.h * exp (openRightSlope u * (x - openLeftLength u)) := by
  have hk := rawFiniteLeft_kink_value u hl
  simp only [halfLineLeftExponent, rawFiniteLeft_one,
    rawFiniteLeft_two] at hk
  simp only [halfLineRightExponent, rawFiniteLeft_one, rawFiniteLeft_two,
    rawFiniteLeft_three, rawFiniteLeft_four]
  rw [← hk, ← Real.exp_add]
  congr 1
  ring

/-! ## Whole-line support: the kink is at zero -/

theorem rawWholeLine_left_weight_eq (u : OpenKinkProfile) (x : ℝ) :
    exp ((rawWholeLine u).c + (rawWholeLine u).beta * x) =
      u.h * exp (openLeftSlope u * x) := by
  dsimp only [rawWholeLine]
  rw [Real.exp_add, Real.exp_log u.h_pos]

theorem rawWholeLine_right_weight_eq (u : OpenKinkProfile) (x : ℝ) :
    exp ((rawWholeLine u).c + (rawWholeLine u).beta * x -
        (rawWholeLine u).delta * (x - (rawWholeLine u).m)) =
      u.h * exp (openRightSlope u * x) := by
  dsimp only [rawWholeLine]
  rw [show log u.h + openLeftSlope u * x -
      (openLeftSlope u - openRightSlope u) * (x - 0) =
        log u.h + openRightSlope u * x by ring,
    Real.exp_add, Real.exp_log u.h_pos]

end LogConcaveFamily6.ProfileDecode

end FlattenedExistenceSection14


/-!
Flattened source section: ProfileQuantileBridge.lean
-/

section FlattenedExistenceSection15

/-!
# Quantile substitution for open one-kink profiles

This file identifies the analytic quantile-profile objective with the
objective of the explicit family-(6) decoder.
-/



open Real Set MeasureTheory intervalIntegral
open scoped Interval

namespace LogConcaveFamily6.ProfileQuantileBridge

open LogConcaveClaimI
open LogConcaveFamily6.ProfileCompactification
open LogConcaveFamily6.ProfileDecode
open LogConcaveFamily6.ProfileEncode
open LogConcaveFamily6.ProfileTailSubstitution

abbrev profileParam (u : OpenKinkProfile) : ProfileParam := openProfileParam u

lemma profileValue_left (u : OpenKinkProfile) {t : ℝ} (ht : t ≤ u.p) :
    profileValue (profileParam u) t = u.h + openLeftSlope u * (t - u.p) := by
  have hp : u.p ≠ 0 := u.p_pos.ne'
  rw [profileValue, dif_pos (by simpa [profileParam, kinkMass] using ht),
    dif_neg (by simpa [profileParam, kinkMass] using hp)]
  simp only [profileParam, kinkMass, leftValue, kinkValue,
    openProfileParam_zero, openProfileParam_one, openProfileParam_two]
  rw [openLeftSlope]
  field_simp [hp]
  ring

lemma profileValue_right (u : OpenKinkProfile) {t : ℝ} (ht : u.p < t) :
    profileValue (profileParam u) t = u.h + openRightSlope u * (t - u.p) := by
  have hp : u.p ≠ 1 := ne_of_lt u.p_lt_one
  rw [profileValue, dif_neg (by simpa [profileParam, kinkMass] using ht),
    dif_neg (by simpa [profileParam, kinkMass] using hp)]
  simp only [profileParam, kinkMass, kinkValue, rightValue,
    openProfileParam_zero, openProfileParam_two, openProfileParam_three]
  rw [openRightSlope]
  field_simp [sub_ne_zero.mpr hp]
  ring

lemma profileValue_right_le (u : OpenKinkProfile) {t : ℝ} (ht : u.p ≤ t) :
    profileValue (profileParam u) t = u.h + openRightSlope u * (t - u.p) := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [profileValue_left u le_rfl]
    ring
  · exact profileValue_right u ht

lemma profileValue_kink (u : OpenKinkProfile) :
    profileValue (profileParam u) u.p = u.h := by
  rw [profileValue_left u le_rfl]
  ring

/-- Raw displacement from the kink on either affine profile segment. -/
def segmentOffset (s h p t : ℝ) : ℝ :=
  if s = 0 then (t - p) / h else log ((h + s * (t - p)) / h) / s

lemma segmentOffset_at_kink (s : ℝ) {h : ℝ} (hh : 0 < h) (p : ℝ) :
    segmentOffset s h p p = 0 := by
  by_cases hs : s = 0
  · simp [segmentOffset, hs]
  · simp [segmentOffset, hs, hh.ne']

lemma hasDerivAt_segmentOffset (s : ℝ) {h : ℝ} (hh : 0 < h)
    (p t : ℝ) (hpos : 0 < h + s * (t - p)) :
    HasDerivAt (segmentOffset s h p)
      ((h + s * (t - p))⁻¹) t := by
  by_cases hs : s = 0
  · subst s
    have hseg : segmentOffset 0 h p = fun x : ℝ ↦ (x - p) / h := by
      funext x
      simp [segmentOffset]
    rw [hseg]
    simpa [id, one_div] using
      ((hasDerivAt_id t).sub_const p).div_const h
  · have ha : HasDerivAt (fun x : ℝ ↦ h + s * (x - p)) s t := by
      have hder := (hasDerivAt_const t h).add
        (((hasDerivAt_id t).sub_const p).const_mul s)
      refine (hder.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards [] with x
        rfl
      · ring
    have hratio : HasDerivAt (fun x : ℝ ↦ (h + s * (x - p)) / h)
        (s / h) t := ha.div_const h
    have hratio_ne : (h + s * (t - p)) / h ≠ 0 :=
      div_ne_zero hpos.ne' hh.ne'
    have hlog := (hratio.log hratio_ne).div_const s
    have hseg : segmentOffset s h p =
        fun x : ℝ ↦ log ((h + s * (x - p)) / h) / s := by
      funext x
      simp [segmentOffset, hs]
    rw [hseg]
    refine hlog.congr_deriv ?_
    field_simp [hs, hh.ne', hpos.ne']

lemma segmentOffset_integral (s : ℝ) {h : ℝ} (hh : 0 < h)
    (p t : ℝ)
    (hpos : ∀ x ∈ uIcc p t, 0 < h + s * (x - p)) :
    (∫ x in p..t, (h + s * (x - p))⁻¹) = segmentOffset s h p t := by
  have hint : IntervalIntegrable (fun x : ℝ ↦ (h + s * (x - p))⁻¹)
      volume p t := by
    exact ((show ContinuousOn (fun x : ℝ ↦ h + s * (x - p)) (uIcc p t) by
      fun_prop).inv₀ (fun x hx ↦ (hpos x hx).ne')).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := segmentOffset s h p)
    (f' := fun x : ℝ ↦ (h + s * (x - p))⁻¹)
    (fun x hx ↦ hasDerivAt_segmentOffset s hh p x (hpos x hx)) hint
  rw [hftc, segmentOffset_at_kink s hh p, sub_zero]

lemma open_profileValue_pos (u : OpenKinkProfile) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < profileValue (profileParam u) t := by
  by_cases htp : t ≤ u.p
  · have hformula := profileValue_left u htp
    have hs := openLeftSlope_mul_p u
    have hnonneg : 0 ≤ (u.p - t) * u.l :=
      mul_nonneg (sub_nonneg.mpr htp) u.l_nonneg
    have hpositive : 0 < t * u.h := mul_pos ht.1 u.h_pos
    rw [hformula]
    have heq : u.p * (u.h + openLeftSlope u * (t - u.p)) =
        (u.p - t) * u.l + t * u.h := by nlinarith [hs]
    have hmul : 0 < u.p * (u.h + openLeftSlope u * (t - u.p)) := by
      rw [heq]
      exact add_pos_of_nonneg_of_pos hnonneg hpositive
    exact pos_of_mul_pos_right hmul u.p_pos.le
  · have hpt : u.p < t := lt_of_not_ge htp
    have hformula := profileValue_right u hpt
    have hs := openRightSlope_mul_one_sub_p u
    have hnonneg : 0 ≤ (t - u.p) * u.r :=
      mul_nonneg (sub_nonneg.mpr hpt.le) u.r_nonneg
    have hpositive : 0 < (1 - t) * u.h :=
      mul_pos (sub_pos.mpr ht.2) u.h_pos
    rw [hformula]
    have hpden : 0 < 1 - u.p := sub_pos.mpr u.p_lt_one
    have heq : (1 - u.p) * (u.h + openRightSlope u * (t - u.p)) =
        (1 - t) * u.h + (t - u.p) * u.r := by nlinarith [hs]
    have hmul : 0 < (1 - u.p) *
        (u.h + openRightSlope u * (t - u.p)) := by
      rw [heq]
      exact add_pos_of_pos_of_nonneg hpositive hnonneg
    exact pos_of_mul_pos_right hmul hpden.le

lemma intervalIntegrable_inv_openProfile (u : OpenKinkProfile)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun t ↦ (profileValue (profileParam u) t)⁻¹)
      volume a b := by
  have hsub : uIcc a b ⊆ Ioo (0 : ℝ) 1 := by
    intro t ht
    rw [mem_uIcc] at ht
    rcases ht with ht | ht
    · exact ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
    · exact ⟨hb.1.trans_le ht.1, ht.2.trans_lt ha.2⟩
  exact (((continuousOn_profileValue_Ioo (profileParam u)).mono hsub).inv₀
    (fun t ht ↦ (open_profileValue_pos u (hsub ht)).ne')).intervalIntegrable

lemma rawQuantile_sub_kink (u : OpenKinkProfile) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    rawQuantile (profileParam u) t - rawQuantile (profileParam u) u.p =
      ∫ s in u.p..t, (profileValue (profileParam u) s)⁻¹ := by
  have hp : u.p ∈ Ioo (0 : ℝ) 1 := ⟨u.p_pos, u.p_lt_one⟩
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  have hI₁ := intervalIntegrable_inv_openProfile u hhalf hp
  have hI₂ := intervalIntegrable_inv_openProfile u hp ht
  have hadd := intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂
  unfold rawQuantile
  linarith

lemma rawQuantile_sub_kink_left (u : OpenKinkProfile) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (htp : t ≤ u.p) :
    rawQuantile (profileParam u) t - rawQuantile (profileParam u) u.p =
      segmentOffset (openLeftSlope u) u.h u.p t := by
  rw [rawQuantile_sub_kink u ht]
  have hp : u.p ∈ Ioo (0 : ℝ) 1 := ⟨u.p_pos, u.p_lt_one⟩
  have hpos : ∀ x ∈ uIcc u.p t,
      0 < u.h + openLeftSlope u * (x - u.p) := by
    intro x hx
    have hxI : x ∈ Ioo (0 : ℝ) 1 := by
      rw [mem_uIcc] at hx
      rcases hx with hx | hx
      · exact ⟨u.p_pos.trans_le hx.1, hx.2.trans_lt ht.2⟩
      · exact ⟨ht.1.trans_le hx.1, hx.2.trans_lt u.p_lt_one⟩
    have hxp : x ≤ u.p := by
      rw [mem_uIcc] at hx
      rcases hx with hx | hx <;> linarith
    rw [← profileValue_left u hxp]
    exact open_profileValue_pos u hxI
  rw [← segmentOffset_integral (openLeftSlope u) u.h_pos u.p t hpos]
  apply intervalIntegral.integral_congr
  intro x hx
  change (profileValue (profileParam u) x)⁻¹ =
    (u.h + openLeftSlope u * (x - u.p))⁻¹
  rw [profileValue_left u]
  rw [mem_uIcc] at hx
  rcases hx with hx | hx <;> linarith

lemma rawQuantile_sub_kink_right (u : OpenKinkProfile) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (hpt : u.p ≤ t) :
    rawQuantile (profileParam u) t - rawQuantile (profileParam u) u.p =
      segmentOffset (openRightSlope u) u.h u.p t := by
  rw [rawQuantile_sub_kink u ht]
  have hp : u.p ∈ Ioo (0 : ℝ) 1 := ⟨u.p_pos, u.p_lt_one⟩
  have hpos : ∀ x ∈ uIcc u.p t,
      0 < u.h + openRightSlope u * (x - u.p) := by
    intro x hx
    have hxI : x ∈ Ioo (0 : ℝ) 1 := by
      rw [mem_uIcc] at hx
      rcases hx with hx | hx
      · exact ⟨u.p_pos.trans_le hx.1, hx.2.trans_lt ht.2⟩
      · exact ⟨ht.1.trans_le hx.1, hx.2.trans_lt u.p_lt_one⟩
    have hpx : u.p ≤ x := by
      rw [mem_uIcc] at hx
      rcases hx with hx | hx <;> linarith
    rw [← profileValue_right_le u hpx]
    exact open_profileValue_pos u hxI
  rw [← segmentOffset_integral (openRightSlope u) u.h_pos u.p t hpos]
  apply intervalIntegral.integral_congr
  intro x hx
  change (profileValue (profileParam u) x)⁻¹ =
    (u.h + openRightSlope u * (x - u.p))⁻¹
  rw [profileValue_right_le u]
  rw [mem_uIcc] at hx
  rcases hx with hx | hx <;> linarith

/-- Kink location used by the raw decoder: zero for a left tail, and the
left segment length when the left endpoint is finite. -/
def rawKinkLocation (u : OpenKinkProfile) : ℝ :=
  if u.l = 0 then 0 else openLeftLength u

/-- The raw quantile reconstructed directly from the two affine pieces of
the quantile-density profile. -/
def canonicalRawQuantile (u : OpenKinkProfile) (t : ℝ) : ℝ :=
  rawKinkLocation u +
    if t ≤ u.p then segmentOffset (openLeftSlope u) u.h u.p t
    else segmentOffset (openRightSlope u) u.h u.p t

lemma canonicalRawQuantile_kink (u : OpenKinkProfile) :
    canonicalRawQuantile u u.p = rawKinkLocation u := by
  simp [canonicalRawQuantile, segmentOffset_at_kink _ u.h_pos]

lemma rawQuantile_eq_canonical_add (u : OpenKinkProfile) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    rawQuantile (profileParam u) t = canonicalRawQuantile u t +
      (rawQuantile (profileParam u) u.p - rawKinkLocation u) := by
  by_cases htp : t ≤ u.p
  · have h := rawQuantile_sub_kink_left u ht htp
    rw [canonicalRawQuantile, if_pos htp]
    linarith
  · have h := rawQuantile_sub_kink_right u ht (le_of_lt (lt_of_not_ge htp))
    rw [canonicalRawQuantile, if_neg htp]
    linarith

def segmentWeight (s h m x : ℝ) : ℝ := h * exp (s * (x - m))

lemma segmentWeight_offset (s : ℝ) {h : ℝ} (hh : 0 < h)
    (p m t : ℝ) (hpos : 0 < h + s * (t - p)) :
    segmentWeight s h m (m + segmentOffset s h p t) =
      h + s * (t - p) := by
  by_cases hs : s = 0
  · simp [segmentWeight, segmentOffset, hs]
  · have hratio : 0 < (h + s * (t - p)) / h := div_pos hpos hh
    rw [segmentWeight, segmentOffset, if_neg hs]
    have hexponent : s *
        (m + log ((h + s * (t - p)) / h) / s - m) =
        log ((h + s * (t - p)) / h) := by
      field_simp [hs]
      ring
    rw [hexponent, exp_log hratio]
    field_simp [hh.ne']

/-- Change of variables on one positive affine profile segment. -/
lemma segment_change_of_variables (q : ℝ → ℝ) (s : ℝ) {h : ℝ}
    (hh : 0 < h) (p m a b : ℝ)
    (hpos : ∀ t ∈ uIcc a b, 0 < h + s * (t - p)) :
    (∫ t in a..b, q (m + segmentOffset s h p t)) =
      ∫ x in (m + segmentOffset s h p a)..(m + segmentOffset s h p b),
        q x * segmentWeight s h m x := by
  let f : ℝ → ℝ := fun t ↦ m + segmentOffset s h p t
  let f' : ℝ → ℝ := fun t ↦ (h + s * (t - p))⁻¹
  let g : ℝ → ℝ := fun x ↦ q x * segmentWeight s h m x
  have hf : ContinuousOn f [[a, b]] := by
    intro t ht
    have ht' : t ∈ uIcc a b := by simpa only [uIcc_of_le, uIcc_of_ge] using ht
    exact ((hasDerivAt_const t m).add
      (hasDerivAt_segmentOffset s hh p t (hpos t ht'))).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Ioo (min a b) (max a b), HasDerivAt f (f' t) t := by
    intro t ht
    have ht' : t ∈ uIcc a b := by
      rw [mem_uIcc]
      by_cases hab : a ≤ b
      · left
        rw [min_eq_left hab, max_eq_right hab] at ht
        exact ⟨ht.1.le, ht.2.le⟩
      · right
        have hba : b ≤ a := le_of_not_ge hab
        rw [min_eq_right hba, max_eq_left hba] at ht
        exact ⟨ht.1.le, ht.2.le⟩
    have hd := (hasDerivAt_const t m).add
      (hasDerivAt_segmentOffset s hh p t (hpos t ht'))
    refine (hd.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [] with x
      rfl
    · simp [f']
  have hnonneg : ∀ t ∈ Ioo (min a b) (max a b), 0 ≤ f' t := by
    intro t ht
    have ht' : t ∈ uIcc a b := by
      rw [mem_uIcc]
      by_cases hab : a ≤ b
      · left
        rw [min_eq_left hab, max_eq_right hab] at ht
        exact ⟨ht.1.le, ht.2.le⟩
      · right
        have hba : b ≤ a := le_of_not_ge hab
        rw [min_eq_right hba, max_eq_left hba] at ht
        exact ⟨ht.1.le, ht.2.le⟩
    exact inv_nonneg.mpr (hpos t ht').le
  have hcv := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (g := g) hf hderiv hnonneg
  change (∫ t in a..b, (g ∘ f) t * f' t) =
      ∫ x in f a..f b, g x at hcv
  rw [← hcv]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ uIcc a b := ht
  have hJ := hpos t ht'
  dsimp only [g, f, f', Function.comp_apply]
  rw [segmentWeight_offset s hh p m t hJ]
  field_simp [hJ.ne']

lemma left_endpoint_offset (u : OpenKinkProfile) (hl : 0 < u.l) :
    openLeftLength u +
      segmentOffset (openLeftSlope u) u.h u.p 0 = 0 := by
  have hslope := openLeftSlope_mul_p u
  have haff : u.h + openLeftSlope u * (0 - u.p) = u.l := by
    nlinarith
  by_cases hs : openLeftSlope u = 0
  · have hhl : u.h = u.l := by
      rw [hs, zero_mul] at hslope
      linarith
    simp [openLeftLength, segmentOffset, hs, hhl]
    field_simp [hl.ne']
    ring
  · rw [openLeftLength, if_neg hs, segmentOffset, if_neg hs, haff]
    rw [Real.log_div u.h_pos.ne' hl.ne', Real.log_div hl.ne' u.h_pos.ne']
    ring

lemma right_endpoint_offset (u : OpenKinkProfile) (hr : 0 < u.r) :
    segmentOffset (openRightSlope u) u.h u.p 1 = openRightLength u := by
  have hslope := openRightSlope_mul_one_sub_p u
  have haff : u.h + openRightSlope u * (1 - u.p) = u.r := by
    nlinarith
  by_cases hs : openRightSlope u = 0
  · have hrh : u.r = u.h := by
      rw [hs, zero_mul] at hslope
      linarith
    simp [openRightLength, segmentOffset, hs, hrh]
  · rw [openRightLength, if_neg hs, segmentOffset, if_neg hs, haff]

lemma left_affine_pos_Icc (u : OpenKinkProfile) (hl : 0 < u.l)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) u.p) :
    0 < u.h + openLeftSlope u * (t - u.p) := by
  have hs := openLeftSlope_mul_p u
  have hnonneg₁ : 0 ≤ (u.p - t) * u.l :=
    mul_nonneg (sub_nonneg.mpr ht.2) hl.le
  have hnonneg₂ : 0 ≤ t * u.h := mul_nonneg ht.1 u.h_pos.le
  have hsum : 0 < (u.p - t) * u.l + t * u.h := by
    by_cases ht0 : t = 0
    · subst t
      simpa using mul_pos u.p_pos hl
    · exact add_pos_of_nonneg_of_pos hnonneg₁
        (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) u.h_pos)
  have heq : u.p * (u.h + openLeftSlope u * (t - u.p)) =
      (u.p - t) * u.l + t * u.h := by nlinarith [hs]
  have hmul : 0 < u.p * (u.h + openLeftSlope u * (t - u.p)) := by
    rwa [heq]
  exact pos_of_mul_pos_right hmul u.p_pos.le

lemma right_affine_pos_Icc (u : OpenKinkProfile) (hr : 0 < u.r)
    {t : ℝ} (ht : t ∈ Icc u.p (1 : ℝ)) :
    0 < u.h + openRightSlope u * (t - u.p) := by
  have hs := openRightSlope_mul_one_sub_p u
  have hnonneg₁ : 0 ≤ (1 - t) * u.h :=
    mul_nonneg (sub_nonneg.mpr ht.2) u.h_pos.le
  have hnonneg₂ : 0 ≤ (t - u.p) * u.r :=
    mul_nonneg (sub_nonneg.mpr ht.1) hr.le
  have hsum : 0 < (1 - t) * u.h + (t - u.p) * u.r := by
    by_cases ht1 : t = 1
    · subst t
      simpa using mul_pos (sub_pos.mpr u.p_lt_one) hr
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)) u.h_pos) hnonneg₂
  have heq : (1 - u.p) * (u.h + openRightSlope u * (t - u.p)) =
      (1 - t) * u.h + (t - u.p) * u.r := by nlinarith [hs]
  have hden : 0 < 1 - u.p := sub_pos.mpr u.p_lt_one
  have hmul : 0 < (1 - u.p) *
      (u.h + openRightSlope u * (t - u.p)) := by rwa [heq]
  exact pos_of_mul_pos_right hmul hden.le

lemma interiorOfOpen_leftSlope (u : OpenKinkProfile) (hl : 0 < u.l)
    (hr : 0 < u.r) :
    leftSlope (interiorOfOpen u hl hr) = openLeftSlope u := rfl

lemma interiorOfOpen_rightSlope (u : OpenKinkProfile) (hl : 0 < u.l)
    (hr : 0 < u.r) :
    rightSlope (interiorOfOpen u hl hr) = openRightSlope u := rfl

lemma interiorOfOpen_leftLength (u : OpenKinkProfile) (hl : 0 < u.l)
    (hr : 0 < u.r) :
    leftLength (interiorOfOpen u hl hr) = openLeftLength u := rfl

lemma interiorOfOpen_rightLength (u : OpenKinkProfile) (hl : 0 < u.l)
    (hr : 0 < u.r) :
    rightLength (interiorOfOpen u hl hr) = openRightLength u := rfl

lemma rawCompact_left_weight_eq_segmentWeight (u : OpenKinkProfile)
    (hl : 0 < u.l) (hr : 0 < u.r) (x : ℝ) :
    exp (leftExponent (rawCompact (interiorOfOpen u hl hr)) x) =
      segmentWeight (openLeftSlope u) u.h (openLeftLength u) x := by
  let v := interiorOfOpen u hl hr
  have hk := rawCompact_kink_value v
  change exp (log u.l + openLeftSlope u * openLeftLength u) = u.h at hk
  rw [segmentWeight, ← hk, ← exp_add]
  change exp (leftExponent (rawCompact v) x) =
    exp ((log u.l + openLeftSlope u * openLeftLength u) +
      openLeftSlope u * (x - openLeftLength u))
  congr 1
  simp only [leftExponent, rawCompact_two, rawCompact_three]
  change log u.l + openLeftSlope u * x = _
  ring

lemma rawCompact_right_weight_eq_segmentWeight (u : OpenKinkProfile)
    (hl : 0 < u.l) (hr : 0 < u.r) (x : ℝ) :
    exp (rightExponent (rawCompact (interiorOfOpen u hl hr)) x) =
      segmentWeight (openRightSlope u) u.h (openLeftLength u) x := by
  let v := interiorOfOpen u hl hr
  have hk := rawCompact_kink_value v
  change exp (log u.l + openLeftSlope u * openLeftLength u) = u.h at hk
  rw [segmentWeight, ← hk, ← exp_add]
  change exp (rightExponent (rawCompact v) x) =
    exp ((log u.l + openLeftSlope u * openLeftLength u) +
      openRightSlope u * (x - openLeftLength u))
  congr 1
  simp only [rightExponent, rawCompact_two, rawCompact_three,
    rawCompact_four, rawCompact_five]
  change log u.l + openLeftSlope u * x -
      (openLeftSlope u - openRightSlope u) *
        (x - openLeftLength u) = _
  ring

lemma compact_leftIntegral_eq_quantile (q : ℝ → ℝ)
    (u : OpenKinkProfile) (hl : 0 < u.l) (hr : 0 < u.r) :
    leftIntegral q (rawCompact (interiorOfOpen u hl hr)) =
      ∫ t in (0 : ℝ)..u.p, q (canonicalRawQuantile u t) := by
  have hpos : ∀ t ∈ uIcc (0 : ℝ) u.p,
      0 < u.h + openLeftSlope u * (t - u.p) := by
    intro t ht
    exact left_affine_pos_Icc u hl (by
      simpa only [uIcc_of_le u.p_pos.le] using ht)
  have hcv := segment_change_of_variables q (openLeftSlope u) u.h_pos
    u.p (openLeftLength u) 0 u.p hpos
  rw [segmentOffset_at_kink _ u.h_pos,
    left_endpoint_offset u hl] at hcv
  simp only [add_zero] at hcv
  calc
    leftIntegral q (rawCompact (interiorOfOpen u hl hr)) =
        ∫ x in (0 : ℝ)..openLeftLength u,
          q x * segmentWeight (openLeftSlope u) u.h
            (openLeftLength u) x := by
      unfold leftIntegral leftIntegrand
      simp only [rawCompact_zero, rawCompact_five, interiorOfOpen_leftLength]
      apply intervalIntegral.integral_congr
      intro x hx
      change q x * exp (leftExponent (rawCompact (interiorOfOpen u hl hr)) x) =
        q x * segmentWeight (openLeftSlope u) u.h (openLeftLength u) x
      rw [rawCompact_left_weight_eq_segmentWeight u hl hr x]
    _ = ∫ t in (0 : ℝ)..u.p,
          q (openLeftLength u +
            segmentOffset (openLeftSlope u) u.h u.p t) := hcv.symm
    _ = ∫ t in (0 : ℝ)..u.p, q (canonicalRawQuantile u t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htp : t ≤ u.p := by
        rw [mem_uIcc] at ht
        rcases ht with ht | ht
        · exact ht.2
        · linarith [u.p_pos]
      change q (openLeftLength u +
        segmentOffset (openLeftSlope u) u.h u.p t) =
        q (canonicalRawQuantile u t)
      rw [canonicalRawQuantile, if_pos htp, rawKinkLocation,
        if_neg hl.ne']

lemma compact_rightIntegral_eq_quantile (q : ℝ → ℝ)
    (u : OpenKinkProfile) (hl : 0 < u.l) (hr : 0 < u.r) :
    rightIntegral q (rawCompact (interiorOfOpen u hl hr)) =
      ∫ t in u.p..(1 : ℝ), q (canonicalRawQuantile u t) := by
  have hpos : ∀ t ∈ uIcc u.p (1 : ℝ),
      0 < u.h + openRightSlope u * (t - u.p) := by
    intro t ht
    exact right_affine_pos_Icc u hr (by
      simpa only [uIcc_of_le u.p_lt_one.le] using ht)
  have hcv := segment_change_of_variables q (openRightSlope u) u.h_pos
    u.p (openLeftLength u) u.p 1 hpos
  rw [segmentOffset_at_kink _ u.h_pos,
    right_endpoint_offset u hr] at hcv
  simp only [add_zero] at hcv
  calc
    rightIntegral q (rawCompact (interiorOfOpen u hl hr)) =
        ∫ x in openLeftLength u..(openLeftLength u + openRightLength u),
          q x * segmentWeight (openRightSlope u) u.h
            (openLeftLength u) x := by
      unfold rightIntegral rightIntegrand
      simp only [rawCompact_five, rawCompact_one, interiorOfOpen_leftLength,
        interiorOfOpen_rightLength]
      apply intervalIntegral.integral_congr
      intro x hx
      change q x * exp (rightExponent (rawCompact (interiorOfOpen u hl hr)) x) =
        q x * segmentWeight (openRightSlope u) u.h (openLeftLength u) x
      rw [rawCompact_right_weight_eq_segmentWeight u hl hr x]
    _ = ∫ t in u.p..(1 : ℝ),
          q (openLeftLength u +
            segmentOffset (openRightSlope u) u.h u.p t) := hcv.symm
    _ = ∫ t in u.p..(1 : ℝ), q (canonicalRawQuantile u t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hpt : u.p ≤ t := by
        rw [mem_uIcc] at ht
        rcases ht with ht | ht
        · exact ht.1
        · linarith [u.p_lt_one]
      change q (openLeftLength u +
        segmentOffset (openRightSlope u) u.h u.p t) =
        q (canonicalRawQuantile u t)
      rcases hpt.eq_or_lt with rfl | hpt
      · rw [canonicalRawQuantile, if_pos le_rfl,
          rawKinkLocation, if_neg hl.ne',
          segmentOffset_at_kink _ u.h_pos,
          segmentOffset_at_kink _ u.h_pos]
      · rw [canonicalRawQuantile, if_neg (not_le_of_gt hpt),
          rawKinkLocation, if_neg hl.ne']

lemma intervalIntegrable_canonical_left (q : ℝ → ℝ) (hq : Continuous q)
    (u : OpenKinkProfile) (hl : 0 < u.l) :
    IntervalIntegrable (fun t ↦ q (canonicalRawQuantile u t)) volume 0 u.p := by
  let e : ℝ → ℝ := fun t ↦ q (openLeftLength u +
    segmentOffset (openLeftSlope u) u.h u.p t)
  have he : ContinuousOn e (uIcc (0 : ℝ) u.p) := by
    intro t ht
    have htI : t ∈ Icc (0 : ℝ) u.p := by
      simpa only [uIcc_of_le u.p_pos.le] using ht
    have hp := left_affine_pos_Icc u hl htI
    have hoff := (hasDerivAt_segmentOffset (openLeftSlope u) u.h_pos u.p t hp).continuousAt
    have hm : ContinuousAt (fun _ : ℝ ↦ openLeftLength u) t := continuousAt_const
    have hcoord0 := hm.add hoff
    have hcoord : ContinuousAt
        (fun x : ℝ ↦ openLeftLength u +
          segmentOffset (openLeftSlope u) u.h u.p x) t := by
      exact hcoord0.congr (Filter.Eventually.of_forall (fun _ ↦ rfl))
    exact (hq.continuousAt.comp hcoord).continuousWithinAt
  have hei : IntervalIntegrable e volume 0 u.p := he.intervalIntegrable
  apply hei.congr_uIoo
  intro t ht
  have htp : t ≤ u.p := by
    rw [uIoo_of_le u.p_pos.le] at ht
    exact ht.2.le
  change e t = q (canonicalRawQuantile u t)
  rw [canonicalRawQuantile, if_pos htp, rawKinkLocation, if_neg hl.ne']

lemma intervalIntegrable_canonical_right (q : ℝ → ℝ) (hq : Continuous q)
    (u : OpenKinkProfile) (hl : 0 < u.l) (hr : 0 < u.r) :
    IntervalIntegrable (fun t ↦ q (canonicalRawQuantile u t)) volume u.p 1 := by
  let e : ℝ → ℝ := fun t ↦ q (openLeftLength u +
    segmentOffset (openRightSlope u) u.h u.p t)
  have he : ContinuousOn e (uIcc u.p (1 : ℝ)) := by
    intro t ht
    have htI : t ∈ Icc u.p (1 : ℝ) := by
      simpa only [uIcc_of_le u.p_lt_one.le] using ht
    have hp := right_affine_pos_Icc u hr htI
    have hoff := (hasDerivAt_segmentOffset (openRightSlope u) u.h_pos u.p t hp).continuousAt
    have hm : ContinuousAt (fun _ : ℝ ↦ openLeftLength u) t := continuousAt_const
    have hcoord0 := hm.add hoff
    have hcoord : ContinuousAt
        (fun x : ℝ ↦ openLeftLength u +
          segmentOffset (openRightSlope u) u.h u.p x) t := by
      exact hcoord0.congr (Filter.Eventually.of_forall (fun _ ↦ rfl))
    exact (hq.continuousAt.comp hcoord).continuousWithinAt
  have hei : IntervalIntegrable e volume u.p 1 := he.intervalIntegrable
  apply hei.congr_uIoo
  intro t ht
  have hpt : u.p < t := by
    rw [uIoo_of_le u.p_lt_one.le] at ht
    exact ht.1
  change e t = q (canonicalRawQuantile u t)
  rw [canonicalRawQuantile, if_neg (not_le_of_gt hpt), rawKinkLocation,
    if_neg hl.ne']

lemma compactIntegral_eq_quantile (q : ℝ → ℝ) (hq : Continuous q)
    (u : OpenKinkProfile) (hl : 0 < u.l) (hr : 0 < u.r) :
    compactIntegral q (rawCompact (interiorOfOpen u hl hr)) =
      ∫ t in (0 : ℝ)..1, q (canonicalRawQuantile u t) := by
  unfold compactIntegral
  rw [compact_leftIntegral_eq_quantile q u hl hr,
    compact_rightIntegral_eq_quantile q u hl hr]
  exact intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_canonical_left q hq u hl)
    (intervalIntegrable_canonical_right q hq u hl hr)

lemma intervalIntegrable_rawQuantile_profile {v : ProfileParam}
    (hv : v ∈ normalizedProfiles) :
    IntervalIntegrable (rawQuantile v) volume 0 1 := by
  have hm : AEStronglyMeasurable (rawQuantile v)
      (volume.restrict (uIoc (0 : ℝ) 1)) := by
    simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using
      aestronglyMeasurable_rawQuantile_Ioc hv
  apply intervalIntegrable_quantileEnvelope.mono_fun' hm
  have hnull : volume ({1} : Set ℝ) = 0 := by simp
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_mono Measure.restrict_le_self (compl_mem_ae_iff.mpr hnull)] with t ht ht1
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
    simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
  have htI : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨htIoc.1, htIoc.2.lt_of_ne (by simpa using ht1)⟩
  rw [Real.norm_eq_abs]
  exact abs_rawQuantile_le_envelope hv htI

def quantileShift (u : OpenKinkProfile) : ℝ :=
  rawQuantile (profileParam u) u.p - rawKinkLocation u

lemma rawQuantile_eq_canonical_add_shift (u : OpenKinkProfile) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    rawQuantile (profileParam u) t =
      canonicalRawQuantile u t + quantileShift u := by
  exact rawQuantile_eq_canonical_add u ht

lemma intervalIntegrable_canonical {u : OpenKinkProfile}
    (hu : profileParam u ∈ normalizedProfiles) :
    IntervalIntegrable (canonicalRawQuantile u) volume 0 1 := by
  have hc : IntervalIntegrable (fun _ : ℝ ↦ quantileShift u) volume 0 1 :=
    intervalIntegrable_const
  have hsub := (intervalIntegrable_rawQuantile_profile hu).sub hc
  apply hsub.congr_uIoo
  intro t ht
  have htI : t ∈ Ioo (0 : ℝ) 1 := by
    simpa only [uIoo_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
  change rawQuantile (profileParam u) t - quantileShift u = canonicalRawQuantile u t
  rw [rawQuantile_eq_canonical_add_shift u htI]
  ring

lemma profileMean_eq_paramMean_add_shift (u : OpenKinkProfile)
    (hu : profileParam u ∈ normalizedProfiles)
    (hpush : paramMean (rawOpenParam u) =
      ∫ t in (0 : ℝ)..1, canonicalRawQuantile u t) :
    profileMean (profileParam u) =
      paramMean (rawOpenParam u) + quantileShift u := by
  have hraw := intervalIntegrable_rawQuantile_profile hu
  have hcan := intervalIntegrable_canonical (u := u) hu
  calc
    profileMean (profileParam u) =
        ∫ t in (0 : ℝ)..1,
          (canonicalRawQuantile u t + quantileShift u) := by
      unfold profileMean
      apply intervalIntegral.integral_congr_ae
      have hnull : volume ({0, 1} : Set ℝ) = 0 := by
        exact Set.toFinite ({0, 1} : Set ℝ) |>.countable.measure_zero volume
      filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht
      intro htmem
      have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
        simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using htmem
      have ht0 : t ≠ 0 := by
        intro hz
        apply ht
        simp [hz]
      have ht1 : t ≠ 1 := by
        intro hz
        apply ht
        simp [hz]
      exact rawQuantile_eq_canonical_add_shift u
        ⟨lt_of_le_of_ne htIoc.1.le (Ne.symm ht0), htIoc.2.lt_of_ne ht1⟩
    _ = (∫ t in (0 : ℝ)..1, canonicalRawQuantile u t) +
          ∫ _t in (0 : ℝ)..1, quantileShift u := by
      rw [intervalIntegral.integral_add hcan intervalIntegrable_const]
    _ = paramMean (rawOpenParam u) + quantileShift u := by
      rw [← hpush]
      simp

lemma segmentOffset_left_zero (u : OpenKinkProfile) (hl : u.l = 0)
    (t : ℝ) :
    segmentOffset (openLeftSlope u) u.h u.p t =
      log (t / u.p) / openLeftSlope u := by
  have hspos := openLeftSlope_pos_of_l_zero u hl
  have hs := openLeftSlope_mul_p u
  rw [hl, sub_zero] at hs
  have hp := u.p_pos.ne'
  have hsne := hspos.ne'
  have harg : (u.h + openLeftSlope u * (t - u.p)) / u.h = t / u.p := by
    field_simp [hp, u.h_pos.ne']
    calc
      u.p * (u.h + openLeftSlope u * (t - u.p)) =
          u.p * u.h + (openLeftSlope u * u.p) * t -
            (openLeftSlope u * u.p) * u.p := by ring
      _ = u.h * t := by rw [hs]; ring
  rw [segmentOffset, if_neg hsne, harg]

lemma segmentOffset_right_zero (u : OpenKinkProfile) (hr : u.r = 0)
    (t : ℝ) :
    segmentOffset (openRightSlope u) u.h u.p t =
      log ((1 - t) / (1 - u.p)) / openRightSlope u := by
  have hsneg := openRightSlope_neg_of_r_zero u hr
  have hs := openRightSlope_mul_one_sub_p u
  rw [hr, zero_sub] at hs
  have hp := (sub_pos.mpr u.p_lt_one).ne'
  have hsne := hsneg.ne
  have harg : (u.h + openRightSlope u * (t - u.p)) / u.h =
      (1 - t) / (1 - u.p) := by
    field_simp [hp, u.h_pos.ne']
    calc
      (u.h + openRightSlope u * (t - u.p)) * (1 - u.p) =
          u.h * (1 - u.p) +
            (openRightSlope u * (1 - u.p)) * (t - u.p) := by ring
      _ = u.h * (1 - t) := by rw [hs]; ring
  rw [segmentOffset, if_neg hsne, harg]

lemma intervalIntegrable_subinterval {f : ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hf : IntervalIntegrable f volume a d) :
    IntervalIntegrable f volume b c := by
  constructor
  · exact hf.1.mono_set (by
      intro x hx
      exact ⟨hab.trans_lt hx.1, hx.2.trans hcd⟩)
  · have hempty : Ioc c b = ∅ := Ioc_eq_empty (not_lt_of_ge hbc)
    rw [hempty]
    exact integrableOn_empty

lemma finiteRight_leftTailIntegral_eq_quantile (q : ℝ → ℝ)
    (u : OpenKinkProfile) (hl : u.l = 0) :
    finiteRightLeftTailIntegral q (rawFiniteRight u) =
      ∫ t in (0 : ℝ)..u.p, q (canonicalRawQuantile u t) := by
  have hspos := openLeftSlope_pos_of_l_zero u hl
  have hcoef := openLeftSlope_mul_p u
  rw [hl, sub_zero] at hcoef
  have htail := integral_Iic_exp_to_interval q hspos u.p_pos hcoef.symm
  calc
    finiteRightLeftTailIntegral q (rawFiniteRight u) =
        ∫ x : ℝ in Iic 0,
          q x * (u.h * exp (openLeftSlope u * x)) := by
      unfold finiteRightLeftTailIntegral finiteRightLeftIntegrand
      simp only [rawFiniteRight_four]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      intro x hx
      change q x * exp (finiteRightLeftExponent (rawFiniteRight u) x) =
        q x * (u.h * exp (openLeftSlope u * x))
      rw [rawFiniteRight_left_weight_eq]
    _ = ∫ t in (0 : ℝ)..u.p,
          q (log (t / u.p) / openLeftSlope u) := htail
    _ = ∫ t in (0 : ℝ)..u.p, q (canonicalRawQuantile u t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htp : t ≤ u.p := by
        rw [mem_uIcc] at ht
        rcases ht with ht | ht
        · exact ht.2
        · linarith [u.p_pos]
      change q (log (t / u.p) / openLeftSlope u) =
        q (canonicalRawQuantile u t)
      rw [canonicalRawQuantile, if_pos htp, rawKinkLocation, if_pos hl,
        zero_add, segmentOffset_left_zero u hl]

lemma finiteRight_rightCompactIntegral_eq_quantile (q : ℝ → ℝ)
    (u : OpenKinkProfile) (hl : u.l = 0) (hr : 0 < u.r) :
    finiteRightRightCompactIntegral q (rawFiniteRight u) =
      ∫ t in u.p..(1 : ℝ), q (canonicalRawQuantile u t) := by
  have hpos : ∀ t ∈ uIcc u.p (1 : ℝ),
      0 < u.h + openRightSlope u * (t - u.p) := by
    intro t ht
    exact right_affine_pos_Icc u hr (by
      simpa only [uIcc_of_le u.p_lt_one.le] using ht)
  have hcv := segment_change_of_variables q (openRightSlope u) u.h_pos
    u.p 0 u.p 1 hpos
  rw [segmentOffset_at_kink _ u.h_pos, right_endpoint_offset u hr] at hcv
  simp only [add_zero, zero_add] at hcv
  calc
    finiteRightRightCompactIntegral q (rawFiniteRight u) =
        ∫ x in (0 : ℝ)..openRightLength u,
          q x * segmentWeight (openRightSlope u) u.h 0 x := by
      unfold finiteRightRightCompactIntegral finiteRightRightIntegrand
      simp only [rawFiniteRight_four, rawFiniteRight_zero]
      apply intervalIntegral.integral_congr
      intro x hx
      change q x * exp (finiteRightRightExponent (rawFiniteRight u) x) =
        q x * segmentWeight (openRightSlope u) u.h 0 x
      rw [rawFiniteRight_right_weight_eq]
      simp [segmentWeight]
    _ = ∫ t in u.p..(1 : ℝ),
          q (segmentOffset (openRightSlope u) u.h u.p t) := hcv.symm
    _ = ∫ t in u.p..(1 : ℝ), q (canonicalRawQuantile u t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hpt : u.p ≤ t := by
        rw [mem_uIcc] at ht
        rcases ht with ht | ht
        · exact ht.1
        · linarith [u.p_lt_one]
      change q (segmentOffset (openRightSlope u) u.h u.p t) =
        q (canonicalRawQuantile u t)
      rcases hpt.eq_or_lt with rfl | hpt
      · rw [canonicalRawQuantile, if_pos le_rfl, rawKinkLocation, if_pos hl,
          segmentOffset_at_kink (openRightSlope u) u.h_pos,
          segmentOffset_at_kink (openLeftSlope u) u.h_pos, zero_add]
      · rw [canonicalRawQuantile, if_neg (not_le_of_gt hpt),
          rawKinkLocation, if_pos hl, zero_add]

lemma finiteLeft_leftCompactIntegral_eq_quantile (q : ℝ → ℝ)
    (u : OpenKinkProfile) (hl : 0 < u.l) :
    halfLineLeftIntegral q (rawFiniteLeft u) =
      ∫ t in (0 : ℝ)..u.p, q (canonicalRawQuantile u t) := by
  have hpos : ∀ t ∈ uIcc (0 : ℝ) u.p,
      0 < u.h + openLeftSlope u * (t - u.p) := by
    intro t ht
    exact left_affine_pos_Icc u hl (by
      simpa only [uIcc_of_le u.p_pos.le] using ht)
  have hcv := segment_change_of_variables q (openLeftSlope u) u.h_pos
    u.p (openLeftLength u) 0 u.p hpos
  rw [segmentOffset_at_kink _ u.h_pos, left_endpoint_offset u hl] at hcv
  simp only [add_zero] at hcv
  calc
    halfLineLeftIntegral q (rawFiniteLeft u) =
        ∫ x in (0 : ℝ)..openLeftLength u,
          q x * segmentWeight (openLeftSlope u) u.h (openLeftLength u) x := by
      unfold halfLineLeftIntegral halfLineLeftIntegrand
      simp only [rawFiniteLeft_zero, rawFiniteLeft_four]
      apply intervalIntegral.integral_congr
      intro x hx
      change q x * exp (halfLineLeftExponent (rawFiniteLeft u) x) =
        q x * segmentWeight (openLeftSlope u) u.h (openLeftLength u) x
      rw [rawFiniteLeft_left_weight_eq u hl]
      simp [segmentWeight]
    _ = ∫ t in (0 : ℝ)..u.p,
          q (openLeftLength u +
            segmentOffset (openLeftSlope u) u.h u.p t) := hcv.symm
    _ = ∫ t in (0 : ℝ)..u.p, q (canonicalRawQuantile u t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htp : t ≤ u.p := by
        rw [mem_uIcc] at ht
        rcases ht with ht | ht
        · exact ht.2
        · linarith [u.p_pos]
      change q (openLeftLength u +
        segmentOffset (openLeftSlope u) u.h u.p t) =
        q (canonicalRawQuantile u t)
      rw [canonicalRawQuantile, if_pos htp, rawKinkLocation,
        if_neg hl.ne']

lemma finiteLeft_rightTailIntegral_eq_quantile (q : ℝ → ℝ)
    (u : OpenKinkProfile) (hl : 0 < u.l) (hr : u.r = 0) :
    halfLineRightIntegral q (rawFiniteLeft u) =
      ∫ t in u.p..(1 : ℝ), q (canonicalRawQuantile u t) := by
  have hsneg := openRightSlope_neg_of_r_zero u hr
  have hcoef0 := openRightSlope_mul_one_sub_p u
  rw [hr, zero_sub] at hcoef0
  have hcoef : u.h = -openRightSlope u * (1 - u.p) := by linarith
  have htail := integral_Ioi_exp_shift_to_interval q hsneg u.p_lt_one hcoef
    (m := openLeftLength u)
  calc
    halfLineRightIntegral q (rawFiniteLeft u) =
        ∫ x : ℝ in Ioi (openLeftLength u),
          q x * (u.h * exp (openRightSlope u * (x - openLeftLength u))) := by
      unfold halfLineRightIntegral halfLineRightIntegrand
      simp only [rawFiniteLeft_four]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change q x * exp (halfLineRightExponent (rawFiniteLeft u) x) =
        q x * (u.h * exp (openRightSlope u * (x - openLeftLength u)))
      rw [rawFiniteLeft_right_weight_eq u hl]
    _ = ∫ t in u.p..(1 : ℝ),
          q (openLeftLength u +
            log ((1 - t) / (1 - u.p)) / openRightSlope u) := htail
    _ = ∫ t in u.p..(1 : ℝ), q (canonicalRawQuantile u t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hpt : u.p ≤ t := by
        rw [mem_uIcc] at ht
        rcases ht with ht | ht
        · exact ht.1
        · linarith [u.p_lt_one]
      change q (openLeftLength u +
          log ((1 - t) / (1 - u.p)) / openRightSlope u) =
        q (canonicalRawQuantile u t)
      rcases hpt.eq_or_lt with rfl | hpt
      · rw [canonicalRawQuantile, if_pos le_rfl, rawKinkLocation,
          if_neg hl.ne', segmentOffset_at_kink (openLeftSlope u) u.h_pos]
        have hz : log ((1 - u.p) / (1 - u.p)) /
            openRightSlope u = 0 := by
          rw [div_self (sub_pos.mpr u.p_lt_one).ne', log_one, zero_div]
        rw [hz]
      · rw [canonicalRawQuantile, if_neg (not_le_of_gt hpt),
          rawKinkLocation, if_neg hl.ne', segmentOffset_right_zero u hr]

lemma wholeLine_leftIntegral_eq_quantile (q : ℝ → ℝ)
    (u : OpenKinkProfile) (hl : u.l = 0) :
    (∫ x : ℝ in Iic 0,
      q x * exp ((rawWholeLine u).c + (rawWholeLine u).beta * x)) =
      ∫ t in (0 : ℝ)..u.p, q (canonicalRawQuantile u t) := by
  have hspos := openLeftSlope_pos_of_l_zero u hl
  have hcoef := openLeftSlope_mul_p u
  rw [hl, sub_zero] at hcoef
  have htail := integral_Iic_exp_to_interval q hspos u.p_pos hcoef.symm
  calc
    (∫ x : ℝ in Iic 0,
        q x * exp ((rawWholeLine u).c + (rawWholeLine u).beta * x)) =
        ∫ x : ℝ in Iic 0,
          q x * (u.h * exp (openLeftSlope u * x)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
      intro x hx
      change q x * exp ((rawWholeLine u).c + (rawWholeLine u).beta * x) =
        q x * (u.h * exp (openLeftSlope u * x))
      rw [rawWholeLine_left_weight_eq]
    _ = ∫ t in (0 : ℝ)..u.p,
          q (log (t / u.p) / openLeftSlope u) := htail
    _ = ∫ t in (0 : ℝ)..u.p, q (canonicalRawQuantile u t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htp : t ≤ u.p := by
        rw [mem_uIcc] at ht
        rcases ht with ht | ht
        · exact ht.2
        · linarith [u.p_pos]
      change q (log (t / u.p) / openLeftSlope u) =
        q (canonicalRawQuantile u t)
      rw [canonicalRawQuantile, if_pos htp, rawKinkLocation, if_pos hl,
        zero_add, segmentOffset_left_zero u hl]

lemma wholeLine_rightIntegral_eq_quantile (q : ℝ → ℝ)
    (u : OpenKinkProfile) (hl : u.l = 0) (hr : u.r = 0) :
    (∫ x : ℝ in Ioi 0,
      q x * exp ((rawWholeLine u).c + (rawWholeLine u).beta * x -
        (rawWholeLine u).delta * (x - (rawWholeLine u).m))) =
      ∫ t in u.p..(1 : ℝ), q (canonicalRawQuantile u t) := by
  have hsneg := openRightSlope_neg_of_r_zero u hr
  have hcoef0 := openRightSlope_mul_one_sub_p u
  rw [hr, zero_sub] at hcoef0
  have hcoef : u.h = -openRightSlope u * (1 - u.p) := by linarith
  have htail := integral_Ioi_exp_to_interval q hsneg u.p_lt_one hcoef
  calc
    (∫ x : ℝ in Ioi 0,
        q x * exp ((rawWholeLine u).c + (rawWholeLine u).beta * x -
          (rawWholeLine u).delta * (x - (rawWholeLine u).m))) =
        ∫ x : ℝ in Ioi 0,
          q x * (u.h * exp (openRightSlope u * x)) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change q x * exp ((rawWholeLine u).c + (rawWholeLine u).beta * x -
          (rawWholeLine u).delta * (x - (rawWholeLine u).m)) =
        q x * (u.h * exp (openRightSlope u * x))
      rw [rawWholeLine_right_weight_eq]
    _ = ∫ t in u.p..(1 : ℝ),
          q (log ((1 - t) / (1 - u.p)) / openRightSlope u) := htail
    _ = ∫ t in u.p..(1 : ℝ), q (canonicalRawQuantile u t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hpt : u.p ≤ t := by
        rw [mem_uIcc] at ht
        rcases ht with ht | ht
        · exact ht.1
        · linarith [u.p_lt_one]
      change q (log ((1 - t) / (1 - u.p)) / openRightSlope u) =
        q (canonicalRawQuantile u t)
      rcases hpt.eq_or_lt with rfl | hpt
      · rw [canonicalRawQuantile, if_pos le_rfl, rawKinkLocation, if_pos hl,
          segmentOffset_at_kink (openLeftSlope u) u.h_pos, zero_add]
        have hz : log ((1 - u.p) / (1 - u.p)) /
            openRightSlope u = 0 := by
          rw [div_self (sub_pos.mpr u.p_lt_one).ne', log_one, zero_div]
        rw [hz]
      · rw [canonicalRawQuantile, if_neg (not_le_of_gt hpt),
          rawKinkLocation, if_pos hl, zero_add, segmentOffset_right_zero u hr]

/-- The raw decoder pushes its density to Lebesgue measure on quantile
levels.  Integrability is assumed only to justify joining the two pieces. -/
theorem rawOpenParam_integral_eq_quantile (q : ℝ → ℝ) (hq : Continuous q)
    (u : OpenKinkProfile)
    (hqint : IntervalIntegrable (fun t ↦ q (canonicalRawQuantile u t))
      volume 0 1) :
    LogConcaveFamily6.integral q (rawOpenParam u) =
      ∫ t in (0 : ℝ)..1, q (canonicalRawQuantile u t) := by
  have hleft : IntervalIntegrable (fun t ↦ q (canonicalRawQuantile u t))
      volume 0 u.p :=
    intervalIntegrable_subinterval le_rfl u.p_pos.le u.p_lt_one.le hqint
  have hright : IntervalIntegrable (fun t ↦ q (canonicalRawQuantile u t))
      volume u.p 1 :=
    intervalIntegrable_subinterval u.p_pos.le u.p_lt_one.le le_rfl hqint
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  by_cases hl0 : u.l = 0
  · by_cases hr0 : u.r = 0
    · have hopen : rawOpenParam u = .wholeLine (rawWholeLine u) := by
        simp [rawOpenParam, hl0, hr0]
      rw [hopen]
      change
        (∫ x : ℝ in Iic 0,
          q x * exp ((rawWholeLine u).c + (rawWholeLine u).beta * x)) +
        (∫ x : ℝ in Ioi 0,
          q x * exp ((rawWholeLine u).c + (rawWholeLine u).beta * x -
            (rawWholeLine u).delta * (x - (rawWholeLine u).m))) = _
      rw [wholeLine_leftIntegral_eq_quantile q u hl0,
        wholeLine_rightIntegral_eq_quantile q u hl0 hr0]
      exact hadd
    · have hr : 0 < u.r := lt_of_le_of_ne u.r_nonneg (Ne.symm hr0)
      have hopen : rawOpenParam u = .finiteRight (rawFiniteRight u) := by
        simp [rawOpenParam, hl0, hr0]
      rw [hopen]
      change finiteRightLeftTailIntegral q (rawFiniteRight u) +
        finiteRightRightCompactIntegral q (rawFiniteRight u) = _
      rw [finiteRight_leftTailIntegral_eq_quantile q u hl0,
        finiteRight_rightCompactIntegral_eq_quantile q u hl0 hr]
      exact hadd
  · have hl : 0 < u.l := lt_of_le_of_ne u.l_nonneg (Ne.symm hl0)
    by_cases hr0 : u.r = 0
    · have hopen : rawOpenParam u = .finiteLeft (rawFiniteLeft u) := by
        simp [rawOpenParam, hl0, hr0]
      rw [hopen]
      change halfLineLeftIntegral q (rawFiniteLeft u) +
        halfLineRightIntegral q (rawFiniteLeft u) = _
      rw [finiteLeft_leftCompactIntegral_eq_quantile q u hl,
        finiteLeft_rightTailIntegral_eq_quantile q u hl hr0]
      exact hadd
    · have hr : 0 < u.r := lt_of_le_of_ne u.r_nonneg (Ne.symm hr0)
      simpa [rawOpenParam, hl0, hr0, LogConcaveFamily6.integral] using
        compactIntegral_eq_quantile q hq u hl hr

theorem rawOpenParam_mean_eq_quantile (u : OpenKinkProfile)
    (hu : profileParam u ∈ normalizedProfiles) :
    paramMean (rawOpenParam u) =
      ∫ t in (0 : ℝ)..1, canonicalRawQuantile u t := by
  simpa only [paramMean] using
    rawOpenParam_integral_eq_quantile (fun x : ℝ ↦ x) continuous_id u
      (intervalIntegrable_canonical (u := u) hu)

theorem profileMean_eq_rawMean_add_shift (u : OpenKinkProfile)
    (hu : profileParam u ∈ normalizedProfiles) :
    profileMean (profileParam u) =
      paramMean (rawOpenParam u) + quantileShift u :=
  profileMean_eq_paramMean_add_shift u hu
    (rawOpenParam_mean_eq_quantile u hu)

lemma centeredQuantile_eq_canonical_sub_rawMean (u : OpenKinkProfile)
    (hu : profileParam u ∈ normalizedProfiles) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    centeredQuantile (profileParam u) t =
      canonicalRawQuantile u t - paramMean (rawOpenParam u) := by
  rw [centeredQuantile, rawQuantile_eq_canonical_add_shift u ht,
    profileMean_eq_rawMean_add_shift u hu]
  ring

lemma rawOpenParam_centered_sq_integral (u : OpenKinkProfile) :
    LogConcaveFamily6.integral
        (fun x : ℝ ↦ (x - paramMean (rawOpenParam u)) ^ 2)
        (rawOpenParam u) = paramVariance (rawOpenParam u) := by
  let p := rawOpenParam u
  have hp := rawOpenParam_admissible u
  have hm := rawOpenParam_mass u
  have hs : (0 : ℝ) < 1 := by norm_num
  have hchange := affineParam_integral (fun x : ℝ ↦ x ^ 2) p
    (paramMean p) 1 hs
  have hmoment := affineParam_secondMoment hp (paramMean p) 1 hs
  change LogConcaveFamily6.integral
      (fun x : ℝ ↦ (x - paramMean p) ^ 2) p = paramVariance p
  have hchange' : paramSecondMoment (affineParam p (paramMean p) 1) =
      LogConcaveFamily6.integral
        (fun x : ℝ ↦ (x - paramMean p) ^ 2) p := by
    simpa only [paramSecondMoment, div_one] using hchange
  rw [← hchange', hmoment, hm]
  unfold paramVariance
  ring

lemma intervalIntegrable_canonical_centered_sq (u : OpenKinkProfile)
    (hu : profileParam u ∈ normalizedProfiles) :
    IntervalIntegrable
      (fun t ↦ (canonicalRawQuantile u t - paramMean (rawOpenParam u)) ^ 2)
      volume 0 1 := by
  apply (intervalIntegrable_centeredQuantile_sq hu).congr_uIoo
  intro t ht
  have htI : t ∈ Ioo (0 : ℝ) 1 := by
    simpa only [uIoo_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
  change centeredQuantile (profileParam u) t ^ 2 =
    (canonicalRawQuantile u t - paramMean (rawOpenParam u)) ^ 2
  rw [centeredQuantile_eq_canonical_sub_rawMean u hu htI]

theorem profileVariance_eq_rawVariance (u : OpenKinkProfile)
    (hu : profileParam u ∈ normalizedProfiles) :
    profileVariance (profileParam u) = paramVariance (rawOpenParam u) := by
  let q : ℝ → ℝ := fun x ↦ (x - paramMean (rawOpenParam u)) ^ 2
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hpush := rawOpenParam_integral_eq_quantile q hq u
    (intervalIntegrable_canonical_centered_sq u hu)
  calc
    profileVariance (profileParam u) =
        ∫ t in (0 : ℝ)..1, q (canonicalRawQuantile u t) := by
      unfold profileVariance
      apply intervalIntegral.integral_congr_ae
      have hnull : volume ({0, 1} : Set ℝ) = 0 :=
        Set.toFinite ({0, 1} : Set ℝ) |>.countable.measure_zero volume
      filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht
      intro htmem
      have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
        simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using htmem
      have ht0 : t ≠ 0 := by intro hz; apply ht; simp [hz]
      have ht1 : t ≠ 1 := by intro hz; apply ht; simp [hz]
      change centeredQuantile (profileParam u) t ^ 2 =
        (canonicalRawQuantile u t - paramMean (rawOpenParam u)) ^ 2
      rw [centeredQuantile_eq_canonical_sub_rawMean u hu
        ⟨lt_of_le_of_ne htIoc.1.le (Ne.symm ht0), htIoc.2.lt_of_ne ht1⟩]
    _ = LogConcaveFamily6.integral q (rawOpenParam u) := hpush.symm
    _ = paramVariance (rawOpenParam u) := rawOpenParam_centered_sq_integral u

theorem profileSigma_eq_rawSigma (u : OpenKinkProfile)
    (hu : profileParam u ∈ normalizedProfiles) :
    profileSigma (profileParam u) = paramSigma (rawOpenParam u) := by
  rw [profileSigma, paramSigma, profileVariance_eq_rawVariance u hu]

lemma standardizedQuantile_eq_canonical_standardized (u : OpenKinkProfile)
    (hu : profileParam u ∈ normalizedProfiles) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    standardizedQuantile (profileParam u) t =
      (canonicalRawQuantile u t - paramMean (rawOpenParam u)) /
        paramSigma (rawOpenParam u) := by
  rw [standardizedQuantile,
    centeredQuantile_eq_canonical_sub_rawMean u hu ht,
    profileSigma_eq_rawSigma u hu]

lemma intervalIntegrable_profile_gAlpha (alpha : ℝ) (halpha : 0 ≤ alpha)
    {v : ProfileParam} (hv : v ∈ normalizedProfiles) :
    IntervalIntegrable
      (fun t ↦ gAlpha alpha (standardizedQuantile v t)) volume 0 1 := by
  have hstd := aestronglyMeasurable_standardizedQuantile_Ioc hv
  have hgIoc : AEStronglyMeasurable
      (fun t ↦ gAlpha alpha (standardizedQuantile v t))
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (continuous_gAlpha alpha).comp_aestronglyMeasurable hstd
  have hg : AEStronglyMeasurable
      (fun t ↦ gAlpha alpha (standardizedQuantile v t))
      (volume.restrict (uIoc (0 : ℝ) 1)) := by
    simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using hgIoc
  have hone : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume 0 1 :=
    intervalIntegrable_const
  apply hone.mono_fun' hg
  exact Filter.Eventually.of_forall (fun t ↦ by
    simpa using abs_gAlpha_le_one halpha (standardizedQuantile v t))

lemma intervalIntegrable_canonical_gAlpha (alpha : ℝ) (halpha : 0 ≤ alpha)
    (u : OpenKinkProfile) (hu : profileParam u ∈ normalizedProfiles) :
    IntervalIntegrable
      (fun t ↦ gAlpha alpha
        ((canonicalRawQuantile u t - paramMean (rawOpenParam u)) /
          paramSigma (rawOpenParam u))) volume 0 1 := by
  apply (intervalIntegrable_profile_gAlpha alpha halpha hu).congr_uIoo
  intro t ht
  have htI : t ∈ Ioo (0 : ℝ) 1 := by
    simpa only [uIoo_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using ht
  change gAlpha alpha (standardizedQuantile (profileParam u) t) =
    gAlpha alpha
      ((canonicalRawQuantile u t - paramMean (rawOpenParam u)) /
        paramSigma (rawOpenParam u))
  rw [standardizedQuantile_eq_canonical_standardized u hu htI]

/-- Exact quantile-substitution bridge for every normalized open-kink
profile, including both half-line and whole-line endpoint cases. -/
theorem openProfileObjective_eq_profileObjective (alpha : ℝ)
    (halpha : 0 ≤ alpha) (u : OpenKinkProfile)
    (hu : profileParam u ∈ normalizedProfiles) :
    openProfileObjective alpha u = profileObjective alpha (profileParam u) := by
  let q : ℝ → ℝ := fun x ↦ gAlpha alpha
    ((x - paramMean (rawOpenParam u)) / paramSigma (rawOpenParam u))
  have hq : Continuous q := by
    dsimp only [q]
    exact (continuous_gAlpha alpha).comp
      ((continuous_id.sub continuous_const).div_const _)
  have hqint : IntervalIntegrable
      (fun t ↦ q (canonicalRawQuantile u t)) volume 0 1 := by
    simpa only [q] using intervalIntegrable_canonical_gAlpha alpha halpha u hu
  have hpush := rawOpenParam_integral_eq_quantile q hq u hqint
  calc
    openProfileObjective alpha u =
        ∫ t in (0 : ℝ)..1, q (canonicalRawQuantile u t) := by
      rw [openProfileObjective]
      exact hpush
    _ = profileObjective alpha (profileParam u) := by
      unfold profileObjective
      symm
      apply intervalIntegral.integral_congr_ae
      have hnull : volume ({0, 1} : Set ℝ) = 0 :=
        Set.toFinite ({0, 1} : Set ℝ) |>.countable.measure_zero volume
      filter_upwards [compl_mem_ae_iff.mpr hnull] with t ht
      intro htmem
      have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
        simpa only [uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] using htmem
      have ht0 : t ≠ 0 := by intro hz; apply ht; simp [hz]
      have ht1 : t ≠ 1 := by intro hz; apply ht; simp [hz]
      change gAlpha alpha (standardizedQuantile (profileParam u) t) =
        q (canonicalRawQuantile u t)
      dsimp only [q]
      rw [standardizedQuantile_eq_canonical_standardized u hu
        ⟨lt_of_le_of_ne htIoc.1.le (Ne.symm ht0), htIoc.2.lt_of_ne ht1⟩]

end LogConcaveFamily6.ProfileQuantileBridge

end FlattenedExistenceSection15


/-!
Flattened source section: Family6ProfileExistence.lean
-/

section FlattenedExistenceSection16

/-!
# Genuine attainment from the exact profile correspondence

The topological part of the existence argument is independent of Claims
(i)--(iii).  This file isolates it: once the elementary quantile substitution
and the exact encoder/decoder inverse are available, compactness of the
normalized profile space produces an actual global maximizer in family (6).
-/



open Set

namespace LogConcaveFamily6.ProfileCompactification

open LogConcaveFamily6.ProfileDecode
open LogConcaveFamily6.ProfileEncode

/-- The abstract final step of the existence proof.  Its two hypotheses are
explicit algebraic/change-of-variables identities, not compactness or
attainment assumptions. -/
theorem exists_family6_globalMax_of_exact_profile_bridges
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hquantile : ∀ v : OpenKinkProfile,
      openProfileObjective alpha v =
        profileObjective alpha (openProfileParam v))
    (hinverse : ∀ (q : LogConcaveFamily6.Param)
      (hq : q ∈ LogConcaveFamily6.family6),
      decodeOpenKink (encodeOpenProfile q hq) = q) :
    ∃ q ∈ LogConcaveFamily6.family6,
      IsMaxOn (LogConcaveFamily6.objective alpha)
        LogConcaveFamily6.family6 q := by
  apply family6_attains_of_profile_correspondence alpha
      (profileObjective alpha) (continuousOn_profileObjective alpha halpha)
  · intro q hq
    let v := encodeOpenProfile q hq
    refine ⟨openProfileParam v, encodeProfile_mem_normalizedProfiles q hq, ?_⟩
    calc
      profileObjective alpha (openProfileParam v) =
          openProfileObjective alpha v := (hquantile v).symm
      _ = LogConcaveFamily6.objective alpha (decodeOpenKink v) :=
        (objective_decodeOpenKink alpha v).symm
      _ = LogConcaveFamily6.objective alpha q := by
        rw [show decodeOpenKink v = q from hinverse q hq]
  · intro u hu
    let v := normalizedOpenProfile u hu
    refine ⟨decodeOpenKink v, decodeOpenKink_mem_family6 v, ?_⟩
    calc
      LogConcaveFamily6.objective alpha (decodeOpenKink v) =
          openProfileObjective alpha v := objective_decodeOpenKink alpha v
      _ = profileObjective alpha (openProfileParam v) := hquantile v
      _ = profileObjective alpha (interiorizeKinkMass u) := by
        rw [openProfileParam_normalizedOpenProfile u hu]
      _ = profileObjective alpha u := profileObjective_interiorizeKinkMass alpha hu

/-- Once quantile substitution is established, exact encoder/decoder recovery
discharges the only other algebraic bridge automatically. -/
theorem exists_family6_globalMax_of_quantile_bridge
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hquantile : ∀ v : OpenKinkProfile,
      openProfileObjective alpha v =
        profileObjective alpha (openProfileParam v)) :
    ∃ q ∈ LogConcaveFamily6.family6,
      IsMaxOn (LogConcaveFamily6.objective alpha)
        LogConcaveFamily6.family6 q := by
  exact exists_family6_globalMax_of_exact_profile_bridges halpha hquantile
    decodeOpenKink_encodeOpenProfile

/-- The form used by the analytic proof: quantile substitution is required
only for normalized profiles, precisely the profiles occurring in the compact
parameter space. -/
theorem exists_family6_globalMax_of_normalized_quantile_bridge
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hquantile : ∀ v : OpenKinkProfile,
      openProfileParam v ∈ normalizedProfiles →
      openProfileObjective alpha v =
        profileObjective alpha (openProfileParam v)) :
    ∃ q ∈ LogConcaveFamily6.family6,
      IsMaxOn (LogConcaveFamily6.objective alpha)
        LogConcaveFamily6.family6 q := by
  apply family6_attains_of_profile_correspondence alpha
      (profileObjective alpha) (continuousOn_profileObjective alpha halpha)
  · intro q hq
    let v := encodeOpenProfile q hq
    have hv : openProfileParam v ∈ normalizedProfiles :=
      encodeProfile_mem_normalizedProfiles q hq
    refine ⟨openProfileParam v, hv, ?_⟩
    calc
      profileObjective alpha (openProfileParam v) =
          openProfileObjective alpha v := (hquantile v hv).symm
      _ = LogConcaveFamily6.objective alpha (decodeOpenKink v) :=
        (objective_decodeOpenKink alpha v).symm
      _ = LogConcaveFamily6.objective alpha q := by
        rw [show decodeOpenKink v = q from decodeOpenKink_encodeOpenProfile q hq]
  · intro u hu
    let v := normalizedOpenProfile u hu
    have hv : openProfileParam v ∈ normalizedProfiles := by
      rw [openProfileParam_normalizedOpenProfile u hu]
      exact interiorizeKinkMass_mem hu
    refine ⟨decodeOpenKink v, decodeOpenKink_mem_family6 v, ?_⟩
    calc
      LogConcaveFamily6.objective alpha (decodeOpenKink v) =
          openProfileObjective alpha v := objective_decodeOpenKink alpha v
      _ = profileObjective alpha (openProfileParam v) := hquantile v hv
      _ = profileObjective alpha (interiorizeKinkMass u) := by
        rw [openProfileParam_normalizedOpenProfile u hu]
      _ = profileObjective alpha u := profileObjective_interiorizeKinkMass alpha hu

/-- **Existence of a genuine global maximizer in family (6).**

The proof uses no compactness assumption on the supports.  The four support
types (compact, left half-line, right half-line, and the whole line) are
encoded in the compact normalized quantile-density profile space; the exact
quantile substitution proved in `ProfileQuantileBridge` transfers a profile
maximizer back to an actual member of `family6`. -/
theorem exists_family6_globalMax
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    ∃ q ∈ LogConcaveFamily6.family6,
      IsMaxOn (LogConcaveFamily6.objective alpha)
        LogConcaveFamily6.family6 q := by
  apply exists_family6_globalMax_of_normalized_quantile_bridge halpha
  intro v hv
  exact LogConcaveFamily6.ProfileQuantileBridge.openProfileObjective_eq_profileObjective
    alpha halpha v hv

end LogConcaveFamily6.ProfileCompactification

end FlattenedExistenceSection16


/-!
Flattened source section: ClaimIII_Clean.lean
-/

section FlattenedExistenceSection17

/-! This single-file artifact proves Claim (iii) of the two-piece-density argument. -/


open MeasureTheory Set Filter Real


/-!
# Exact integrals for the asymmetric-Laplace family

This file evaluates the one-dimensional integrals occurring in the
asymmetric-Laplace part of Theorem 2.
-/

/-- The elementary half-line integral used in all subsequent evaluations. -/
lemma integral_linear_exp_Ioi
    (A B lambda lower : ℝ) (hlambda : 0 < lambda)
    (hlin : ∀ t ∈ Ioi lower, 0 ≤ A + B * t) :
    (∫ t : ℝ in Ioi lower, (A + B * t) * Real.exp (-lambda * t)) =
      Real.exp (-lambda * lower) *
        (A / lambda + B * lower / lambda + B / lambda ^ 2) := by
  let F : ℝ → ℝ := fun t =>
    -(Real.exp (-lambda * t) *
      (A / lambda + B * t / lambda + B / lambda ^ 2))
  have hderiv : ∀ t ∈ Ici lower,
      HasDerivAt F ((A + B * t) * Real.exp (-lambda * t)) t := by
    intro t ht
    have hi : HasDerivAt (fun x : ℝ => -lambda * x) (-lambda) t := by
      simpa using (hasDerivAt_id t).const_mul (-lambda)
    have he : HasDerivAt (fun x : ℝ => Real.exp (-lambda * x))
        (-lambda * Real.exp (-lambda * t)) t := by
      simpa [mul_comm] using hi.exp
    have hlinear : HasDerivAt (fun x : ℝ => B * x / lambda)
        (B / lambda) t := by
      simpa using ((hasDerivAt_id t).const_mul B).div_const lambda
    have hc : HasDerivAt
        (fun x : ℝ => A / lambda + B * x / lambda + B / lambda ^ 2)
        (B / lambda) t := by
      simpa only [add_assoc] using
        (hlinear.const_add (A / lambda)).add_const (B / lambda ^ 2)
    have hraw := (he.mul hc).neg
    have hrawF : HasDerivAt F
        (-((-lambda * Real.exp (-lambda * t)) *
            (A / lambda + B * t / lambda + B / lambda ^ 2) +
          Real.exp (-lambda * t) * (B / lambda))) t := by
      apply hraw.congr_of_eventuallyEq
      filter_upwards with x
      simp only [F, Pi.neg_apply, Pi.mul_apply]
    apply hrawF.congr_deriv
    field_simp [hlambda.ne']
    ring
  have he0 : Tendsto (fun t : ℝ => Real.exp (-lambda * t)) atTop (nhds 0) :=
    tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hlambda))
  have ht0 : Tendsto
      (fun t : ℝ => t * Real.exp (-lambda * t)) atTop (nhds 0) := by
    simpa using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) lambda hlambda)
  have hlim : Tendsto F atTop (nhds 0) := by
    have hleft := he0.const_mul (A / lambda + B / lambda ^ 2)
    have hright := ht0.const_mul (B / lambda)
    have hsum := hleft.add hright
    convert hsum.neg using 1
    · funext t
      simp [F]
      ring
    · simp
  have hFTC := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := F)
    (g' := fun t : ℝ => (A + B * t) * Real.exp (-lambda * t))
    hderiv
    (fun t ht => mul_nonneg (hlin t ht) (Real.exp_pos _).le)
    hlim
  simpa [F] using hFTC

/-- The corresponding elementary integral over a finite oriented interval. -/
lemma intervalIntegral_linear_exp
    (A B lambda u v : ℝ) (hlambda : lambda ≠ 0) :
    (∫ t : ℝ in u..v, (A + B * t) * Real.exp (-lambda * t)) =
      -(Real.exp (-lambda * v) *
          (A / lambda + B * v / lambda + B / lambda ^ 2)) +
        Real.exp (-lambda * u) *
          (A / lambda + B * u / lambda + B / lambda ^ 2) := by
  let F : ℝ → ℝ := fun t =>
    -(Real.exp (-lambda * t) *
      (A / lambda + B * t / lambda + B / lambda ^ 2))
  have hderiv : ∀ t : ℝ,
      HasDerivAt F ((A + B * t) * Real.exp (-lambda * t)) t := by
    intro t
    have hi : HasDerivAt (fun x : ℝ => -lambda * x) (-lambda) t := by
      simpa using (hasDerivAt_id t).const_mul (-lambda)
    have he : HasDerivAt (fun x : ℝ => Real.exp (-lambda * x))
        (-lambda * Real.exp (-lambda * t)) t := by
      simpa [mul_comm] using hi.exp
    have hlinear : HasDerivAt (fun x : ℝ => B * x / lambda)
        (B / lambda) t := by
      simpa using ((hasDerivAt_id t).const_mul B).div_const lambda
    have hc : HasDerivAt
        (fun x : ℝ => A / lambda + B * x / lambda + B / lambda ^ 2)
        (B / lambda) t := by
      simpa only [add_assoc] using
        (hlinear.const_add (A / lambda)).add_const (B / lambda ^ 2)
    have hraw := (he.mul hc).neg
    have hrawF : HasDerivAt F
        (-((-lambda * Real.exp (-lambda * t)) *
            (A / lambda + B * t / lambda + B / lambda ^ 2) +
          Real.exp (-lambda * t) * (B / lambda))) t := by
      apply hraw.congr_of_eventuallyEq
      filter_upwards with x
      simp only [F, Pi.neg_apply, Pi.mul_apply]
    apply hrawF.congr_deriv
    field_simp [hlambda]
    ring
  have hint : IntervalIntegrable
      (fun t : ℝ => (A + B * t) * Real.exp (-lambda * t)) volume u v := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F)
    (f' := fun t : ℝ => (A + B * t) * Real.exp (-lambda * t))
    (fun t ht => hderiv t) hint
  simpa [F] using hFTC

/-- The test function in Theorem 2. -/
def gAlpha (alpha r : ℝ) : ℝ :=
  (1 + alpha * r) * Real.exp (-alpha * r)

lemma gAlpha_nonneg {alpha r : ℝ} (halpha : 0 ≤ alpha) (hr : 0 ≤ r) :
    0 ≤ gAlpha alpha r := by
  exact mul_nonneg (add_nonneg zero_le_one (mul_nonneg halpha hr))
    (Real.exp_pos _).le

lemma gAlpha_le_one {alpha r : ℝ} (halpha : 0 ≤ alpha) (hr : 0 ≤ r) :
    gAlpha alpha r ≤ 1 := by
  let x := alpha * r
  have hx : 0 ≤ x := mul_nonneg halpha hr
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x)
    (Real.exp_pos (-x)).le
  calc
    gAlpha alpha r = (x + 1) * Real.exp (-x) := by
      simp [gAlpha, x]
      ring
    _ ≤ Real.exp x * Real.exp (-x) := h
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The shifted-exponential integrand is integrable on its whole half-line. -/
lemma integrableOn_shiftedIntegrand (alpha : ℝ) (halpha : 0 ≤ alpha) :
    IntegrableOn
      (fun t : ℝ => gAlpha alpha |1 - t| * Real.exp (-t)) (Ioi 0) := by
  refine (integrableOn_exp_neg_Ioi 0).mono' ?_ ?_
  · have hcont : Continuous
        (fun t : ℝ => gAlpha alpha |1 - t| * Real.exp (-t)) := by
      unfold gAlpha
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards with t
    have hg0 : 0 ≤ gAlpha alpha |1 - t| :=
      gAlpha_nonneg halpha (abs_nonneg _)
    change |gAlpha alpha |1 - t| * Real.exp (-t)| ≤ Real.exp (-t)
    rw [abs_of_nonneg (mul_nonneg hg0 (Real.exp_pos _).le)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le
      (gAlpha_le_one halpha (abs_nonneg _))

/-- Uniform integrability for either exponential ray. -/
lemma integrableOn_rayIntegrand
    (alpha d scale : ℝ) (halpha : 0 ≤ alpha) :
    IntegrableOn
      (fun t : ℝ => gAlpha alpha |d + scale * t| * Real.exp (-t)) (Ioi 0) := by
  refine (integrableOn_exp_neg_Ioi 0).mono' ?_ ?_
  · have hcont : Continuous
        (fun t : ℝ => gAlpha alpha |d + scale * t| * Real.exp (-t)) := by
      unfold gAlpha
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards with t
    have hg0 : 0 ≤ gAlpha alpha |d + scale * t| :=
      gAlpha_nonneg halpha (abs_nonneg _)
    change |gAlpha alpha |d + scale * t| * Real.exp (-t)| ≤ Real.exp (-t)
    rw [abs_of_nonneg (mul_nonneg hg0 (Real.exp_pos _).le)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le
      (gAlpha_le_one halpha (abs_nonneg _))

/-- The expectation for the centered asymmetric-Laplace law with ray scales
`a` and `b`.  This one-dimensional formula remains meaningful at `a = 0`
or `b = 0`. -/
def asymLaplaceObjective (alpha a b : ℝ) : ℝ :=
  let d := a - b
  a / (a + b) *
      (∫ t in Ioi (0 : ℝ),
        gAlpha alpha |d - a * t| * Real.exp (-t)) +
    b / (a + b) *
      (∫ t in Ioi (0 : ℝ),
        gAlpha alpha |d + b * t| * Real.exp (-t))

/-- Interchanging the two exponential rays only reflects the law, so the
even objective is unchanged. -/
theorem asymLaplaceObjective_swap (alpha a b : ℝ) :
    asymLaplaceObjective alpha a b = asymLaplaceObjective alpha b a := by
  have hleft :
      (∫ t in Ioi (0 : ℝ),
        gAlpha alpha |(b - a) - b * t| * Real.exp (-t)) =
      (∫ t in Ioi (0 : ℝ),
        gAlpha alpha |(a - b) + b * t| * Real.exp (-t)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change gAlpha alpha |(b - a) - b * t| * Real.exp (-t) =
      gAlpha alpha |(a - b) + b * t| * Real.exp (-t)
    rw [show (b - a) - b * t = -((a - b) + b * t) by ring, abs_neg]
  have hright :
      (∫ t in Ioi (0 : ℝ),
        gAlpha alpha |(b - a) + a * t| * Real.exp (-t)) =
      (∫ t in Ioi (0 : ℝ),
        gAlpha alpha |(a - b) - a * t| * Real.exp (-t)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change gAlpha alpha |(b - a) + a * t| * Real.exp (-t) =
      gAlpha alpha |(a - b) - a * t| * Real.exp (-t)
    rw [show (b - a) + a * t = -((a - b) - a * t) by ring, abs_neg]
  change
    a / (a + b) *
        (∫ t in Ioi (0 : ℝ),
          gAlpha alpha |(a - b) - a * t| * Real.exp (-t)) +
      b / (a + b) *
        (∫ t in Ioi (0 : ℝ),
          gAlpha alpha |(a - b) + b * t| * Real.exp (-t)) =
    b / (b + a) *
        (∫ t in Ioi (0 : ℝ),
          gAlpha alpha |(b - a) - b * t| * Real.exp (-t)) +
      a / (b + a) *
        (∫ t in Ioi (0 : ℝ),
          gAlpha alpha |(b - a) + a * t| * Real.exp (-t))
  rw [hleft, hright]
  ring

/-! ## The normalized regular asymmetric-Laplace family -/

/-- Exact evaluation of the ray whose absolute value changes sign at `q`. -/
theorem normalizedFirstRay_formula
    (z q : ℝ) (hz : 0 ≤ z) (hq : 0 ≤ q) :
    (∫ t : ℝ in Ioi 0, gAlpha z |q - t| * Real.exp (-t)) =
      Real.exp (-q) *
        ((1 + 2 * z) / (1 + z) ^ 2 +
          ∫ t : ℝ in Ioc 0 q, (1 + z * t) * Real.exp ((1 - z) * t)) := by
  have hint : IntegrableOn
      (fun t : ℝ => gAlpha z |q - t| * Real.exp (-t)) (Ioi 0) := by
    simpa [sub_eq_add_neg] using integrableOn_rayIntegrand z q (-1) hz
  have htailInt : IntegrableOn
      (fun t : ℝ => gAlpha z |q - t| * Real.exp (-t)) (Ioi q) :=
    hint.mono_set (Ioi_subset_Ioi hq)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint htailInt
  let phi : ℝ → ℝ := fun u => (1 + z * u) * Real.exp ((1 - z) * u)
  have hfinite :
      (∫ t : ℝ in 0..q, gAlpha z |q - t| * Real.exp (-t)) =
        Real.exp (-q) * (∫ u : ℝ in Ioc 0 q, phi u) := by
    calc
      _ = (∫ t : ℝ in 0..q, Real.exp (-q) * phi (q - t)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) q := by
          simpa [uIcc_of_le hq] using ht
        have hqt : 0 ≤ q - t := sub_nonneg.mpr ht'.2
        change gAlpha z |q - t| * Real.exp (-t) = _
        rw [abs_of_nonneg hqt]
        simp only [gAlpha, phi]
        have hexp : Real.exp (-z * (q - t)) * Real.exp (-t) =
            Real.exp (-q) * Real.exp ((1 - z) * (q - t)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [mul_assoc, hexp]
        ring
      _ = Real.exp (-q) * (∫ t : ℝ in 0..q, phi (q - t)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = Real.exp (-q) * (∫ u : ℝ in q - q..q - 0, phi u) := by
        rw [intervalIntegral.integral_comp_sub_left]
      _ = _ := by
        simp only [sub_self, sub_zero]
        rw [intervalIntegral.integral_of_le hq]
  have hlambda : 0 < 1 + z := by positivity
  have hbase := integral_linear_exp_Ioi
    (1 - z * q) z (1 + z) q hlambda (by
      intro t ht
      have hprod : 0 ≤ z * (t - q) :=
        mul_nonneg hz (sub_nonneg.mpr ht.le)
      nlinarith)
  have htail :
      (∫ t : ℝ in Ioi q, gAlpha z |q - t| * Real.exp (-t)) =
        Real.exp (-q) * (1 + 2 * z) / (1 + z) ^ 2 := by
    calc
      _ = (∫ t : ℝ in Ioi q,
          Real.exp (z * q) *
            ((1 - z * q + z * t) * Real.exp (-(1 + z) * t))) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have hqt : q - t ≤ 0 := sub_nonpos.mpr ht.le
        change gAlpha z |q - t| * Real.exp (-t) = _
        rw [abs_of_nonpos hqt]
        simp only [gAlpha]
        have hcoeff : 1 + z * (-(q - t)) = 1 - z * q + z * t := by ring
        have hexp : Real.exp (-z * (-(q - t))) * Real.exp (-t) =
            Real.exp (z * q) * Real.exp (-(1 + z) * t) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [hcoeff, mul_assoc, hexp]
        ring
      _ = Real.exp (z * q) *
          (∫ t : ℝ in Ioi q,
            (1 - z * q + z * t) * Real.exp (-(1 + z) * t)) := by
        rw [MeasureTheory.integral_const_mul]
      _ = Real.exp (z * q) *
          (Real.exp (-(1 + z) * q) *
            ((1 - z * q) / (1 + z) + z * q / (1 + z) +
              z / (1 + z) ^ 2)) := by rw [hbase]
      _ = _ := by
        have hexp : Real.exp (z * q) * Real.exp (-(1 + z) * q) =
            Real.exp (-q) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [show Real.exp (z * q) *
            (Real.exp (-(1 + z) * q) *
              ((1 - z * q) / (1 + z) + z * q / (1 + z) +
                z / (1 + z) ^ 2)) =
            (Real.exp (z * q) * Real.exp (-(1 + z) * q)) *
              ((1 - z * q) / (1 + z) + z * q / (1 + z) +
                z / (1 + z) ^ 2) by ring]
        rw [hexp]
        field_simp [hlambda.ne']
        ring
  rw [← hsplit, hfinite, htail]
  dsimp [phi]
  ring

/-- Exact evaluation of the ray which stays on the positive side. -/
theorem normalizedSecondRay_formula
    (z p q : ℝ) (hz : 0 ≤ z) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (∫ t : ℝ in Ioi 0, gAlpha z |q + p * t| * Real.exp (-t)) =
      Real.exp (-z * q) *
        ((1 + z * q) / (1 + z * p) + z * p / (1 + z * p) ^ 2) := by
  have hlambda : 0 < 1 + z * p := by positivity
  have hbase := integral_linear_exp_Ioi
    (1 + z * q) (z * p) (1 + z * p) 0 hlambda (by
      intro t ht
      exact add_nonneg (add_nonneg zero_le_one (mul_nonneg hz hq))
        (mul_nonneg (mul_nonneg hz hp) ht.le))
  calc
    _ = (∫ t : ℝ in Ioi 0,
        Real.exp (-z * q) *
          ((1 + z * q + z * p * t) * Real.exp (-(1 + z * p) * t))) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have hnonneg : 0 ≤ q + p * t :=
        add_nonneg hq (mul_nonneg hp ht.le)
      change gAlpha z |q + p * t| * Real.exp (-t) = _
      rw [abs_of_nonneg hnonneg]
      simp only [gAlpha]
      have hcoeff : 1 + z * (q + p * t) =
          1 + z * q + z * p * t := by ring
      have hexp : Real.exp (-z * (q + p * t)) * Real.exp (-t) =
          Real.exp (-z * q) * Real.exp (-(1 + z * p) * t) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [hcoeff, mul_assoc, hexp]
      ring
    _ = Real.exp (-z * q) *
        (∫ t : ℝ in Ioi 0,
          (1 + z * q + z * p * t) * Real.exp (-(1 + z * p) * t)) := by
      rw [MeasureTheory.integral_const_mul]
    _ = Real.exp (-z * q) *
        (Real.exp (-(1 + z * p) * 0) *
          ((1 + z * q) / (1 + z * p) + z * p * 0 / (1 + z * p) +
            z * p / (1 + z * p) ^ 2)) := by rw [hbase]
    _ = _ := by simp

/-- The scale `a` in the regular parametrization `b = p a`. -/
def regularScale (p : ℝ) : ℝ :=
  1 / Real.sqrt (1 + p ^ 2)

/-- The closed formula used by the one-variable calculus argument. -/
def kHatRegular (alpha p : ℝ) : ℝ :=
  let a := regularScale p
  let z := alpha * a
  let q := 1 - p
  1 / (1 + p) *
    (Real.exp (-q) *
        ((1 + 2 * z) / (1 + z) ^ 2 +
          ∫ t : ℝ in Ioc 0 q, (1 + z * t) * Real.exp ((1 - z) * t)) +
      Real.exp (-z * q) *
        (p * (1 + z * q) / (1 + z * p) +
          z * p ^ 2 / (1 + z * p) ^ 2))

/-- The rational coefficient of `exp (-z(1-p))` after evaluating the
finite integral in `kHatRegular`. -/
def regularA (p z : ℝ) : ℝ :=
  (1 - z - z ^ 2 + z * (1 - z - z ^ 2) * p -
      z ^ 2 * (1 - z) * p ^ 2) /
    ((1 - z) ^ 2 * (1 + z * p) ^ 2)

/-- The rational coefficient of `exp (p-1)` after evaluating the finite
integral in `kHatRegular`. -/
def regularB (p z : ℝ) : ℝ :=
  4 * z ^ 3 / ((1 + p) * (1 - z ^ 2) ^ 2)

/-- The coefficient of `exp (-z(1-p))` in the raw integral evaluation
simplifies to `regularA`. -/
lemma regularA_identity
    (p z : ℝ) (hpden : 1 + p ≠ 0) (hz1 : z ≠ 1)
    (hzp : 1 + z * p ≠ 0) :
    (p * (1 + z * (1 - p)) / (1 + z * p) +
          z * p ^ 2 / (1 + z * p) ^ 2 -
          (1 / (z - 1) + z * (1 - p) / (z - 1) +
            z / (z - 1) ^ 2)) /
        (1 + p) = regularA p z := by
  have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hsubz : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  let d : ℝ := 1 + z * p
  have hd : d ≠ 0 := by simpa [d] using hzp
  have hden : (1 - z) ^ 2 * d ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hsubz) (pow_ne_zero 2 hd)
  change
    (p * (1 + z * (1 - p)) / d + z * p ^ 2 / d ^ 2 -
          (1 / (z - 1) + z * (1 - p) / (z - 1) +
            z / (z - 1) ^ 2)) /
        (1 + p) =
      (1 - z - z ^ 2 + z * (1 - z - z ^ 2) * p -
          z ^ 2 * (1 - z) * p ^ 2) /
        ((1 - z) ^ 2 * d ^ 2)
  apply (div_eq_div_iff hpden hden).2
  field_simp [hzsub, hd]
  ring

/-- The coefficient of `exp (p-1)` in the raw integral evaluation
simplifies to `regularB`. -/
lemma regularB_identity
    (p z : ℝ) (hpden : 1 + p ≠ 0) (hz1 : z ≠ 1)
    (hzplus : 1 + z ≠ 0) :
    ((1 + 2 * z) / (1 + z) ^ 2 +
          (1 / (z - 1) + z / (z - 1) ^ 2)) /
        (1 + p) = regularB p z := by
  have hzsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hsubz : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have hsq : 1 - z ^ 2 ≠ 0 := by
    rw [show 1 - z ^ 2 = (1 - z) * (1 + z) by ring]
    exact mul_ne_zero hsubz hzplus
  unfold regularB
  field_simp [hpden, hzsub, hzplus, hsq]
  ring

/-- Closed evaluation of the finite integral, away from its removable
singularity at `z=1`. -/
theorem finiteIoc_formula
    (z q : ℝ) (hq : 0 ≤ q) (hz1 : z ≠ 1) :
    (∫ t : ℝ in Ioc 0 q, (1 + z * t) * Real.exp ((1 - z) * t)) =
      -(Real.exp ((1 - z) * q) *
          (1 / (z - 1) + z * q / (z - 1) + z / (z - 1) ^ 2)) +
        (1 / (z - 1) + z / (z - 1) ^ 2) := by
  have hlambda : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have hbase := intervalIntegral_linear_exp 1 z (z - 1) 0 q hlambda
  calc
    _ = (∫ t : ℝ in 0..q, (1 + z * t) * Real.exp ((1 - z) * t)) := by
      rw [intervalIntegral.integral_of_le hq]
    _ = (∫ t : ℝ in 0..q, (1 + z * t) * Real.exp (-(z - 1) * t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change (1 + z * t) * Real.exp ((1 - z) * t) =
        (1 + z * t) * Real.exp (-(z - 1) * t)
      rw [show (1 - z) * t = -(z - 1) * t by ring]
    _ = -(Real.exp (-(z - 1) * q) *
          (1 / (z - 1) + z * q / (z - 1) + z / (z - 1) ^ 2)) +
        Real.exp (-(z - 1) * 0) *
          (1 / (z - 1) + z * 0 / (z - 1) + z / (z - 1) ^ 2) := by
      simpa using hbase
    _ = _ := by
      have hexp : Real.exp (-(z - 1) * q) = Real.exp ((1 - z) * q) := by
        congr 1
        ring
      rw [hexp]
      simp

lemma regularScale_pos (p : ℝ) : 0 < regularScale p := by
  unfold regularScale
  have : 0 < 1 + p ^ 2 := by nlinarith [sq_nonneg p]
  positivity

lemma regularScale_isotropic (p : ℝ) :
    regularScale p ^ 2 + (p * regularScale p) ^ 2 = 1 := by
  have hspos : 0 < Real.sqrt (1 + p ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_nonneg p]
  have hsquare : (Real.sqrt (1 + p ^ 2)) ^ 2 = 1 + p ^ 2 :=
    Real.sq_sqrt (by nlinarith [sq_nonneg p])
  unfold regularScale
  field_simp [hspos.ne']
  nlinarith

/-- Away from the removable singularity `z=1`, the integral formula
`kHatRegular` is the two-exponential expression used by the calculus
certificate. -/
theorem kHatRegular_eq_exp_regular
    (alpha p : ℝ) (halpha : 0 ≤ alpha) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hz1 : alpha * regularScale p ≠ 1) :
    kHatRegular alpha p =
      Real.exp (-(alpha * regularScale p * (1 - p))) *
          regularA p (alpha * regularScale p) +
        Real.exp (p - 1) * regularB p (alpha * regularScale p) := by
  let z : ℝ := alpha * regularScale p
  let q : ℝ := 1 - p
  let R : ℝ := (1 + 2 * z) / (1 + z) ^ 2
  let Tq : ℝ :=
    1 / (z - 1) + z * q / (z - 1) + z / (z - 1) ^ 2
  let T0 : ℝ := 1 / (z - 1) + z / (z - 1) ^ 2
  let S : ℝ :=
    p * (1 + z * q) / (1 + z * p) + z * p ^ 2 / (1 + z * p) ^ 2
  have hz : 0 ≤ z :=
    mul_nonneg halpha (regularScale_pos p).le
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hz1' : z ≠ 1 := by simpa [z] using hz1
  have hpden : 1 + p ≠ 0 := by linarith
  have hzplus : 1 + z ≠ 0 := by positivity
  have hzp : 1 + z * p ≠ 0 := by positivity
  have hI :
      (∫ t : ℝ in Ioc 0 q,
          (1 + z * t) * Real.exp ((1 - z) * t)) =
        -(Real.exp ((1 - z) * q) * Tq) + T0 := by
    simpa [Tq, T0] using finiteIoc_formula z q hq hz1'
  have hA : (S - Tq) / (1 + p) = regularA p z := by
    simpa [S, Tq, q] using
      regularA_identity p z hpden hz1' hzp
  have hB : (R + T0) / (1 + p) = regularB p z := by
    simpa [R, T0] using
      regularB_identity p z hpden hz1' hzplus
  have hexpmix :
      Real.exp (-q) * Real.exp ((1 - z) * q) =
        Real.exp (-z * q) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hexpq : Real.exp (-q) = Real.exp (p - 1) := by
    congr 1
    dsimp [q]
    ring
  calc
    kHatRegular alpha p =
        1 / (1 + p) *
          (Real.exp (-q) *
              (R + ∫ t : ℝ in Ioc 0 q,
                (1 + z * t) * Real.exp ((1 - z) * t)) +
            Real.exp (-z * q) * S) := by
      rfl
    _ = 1 / (1 + p) *
          (Real.exp (-q) *
              (R + (-(Real.exp ((1 - z) * q) * Tq) + T0)) +
            Real.exp (-z * q) * S) := by rw [hI]
    _ = (Real.exp (-q) * Real.exp ((1 - z) * q)) *
            ((S - Tq) / (1 + p)) +
          Real.exp (-q) * ((R + T0) / (1 + p)) := by
      rw [← hexpmix]
      field_simp [hpden]
      ring
    _ = Real.exp (-z * q) * regularA p z +
          Real.exp (-q) * regularB p z := by
      rw [hexpmix, hA, hB]
    _ = _ := by
      rw [hexpq]
      simp [z, q]

/-- The genuine asymmetric-Laplace expectation agrees with the regular
one-variable formula. -/
theorem asymLaplaceObjective_regular
    (alpha p : ℝ) (halpha : 0 ≤ alpha) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    asymLaplaceObjective alpha (regularScale p) (p * regularScale p) =
      kHatRegular alpha p := by
  let a : ℝ := regularScale p
  let z : ℝ := alpha * a
  let q : ℝ := 1 - p
  have ha : 0 < a := by simpa [a] using regularScale_pos p
  have hz : 0 ≤ z := mul_nonneg halpha ha.le
  have hq : 0 ≤ q := sub_nonneg.mpr hp1
  have h1p : 0 < 1 + p := by linarith
  have hweight1 : a / (a + p * a) = 1 / (1 + p) := by
    field_simp [ha.ne', h1p.ne']
  have hweight2 : p * a / (a + p * a) = p / (1 + p) := by
    field_simp [ha.ne', h1p.ne']
  have hfirstChange :
      (∫ t : ℝ in Ioi 0,
        gAlpha alpha |(a - p * a) - a * t| * Real.exp (-t)) =
      (∫ t : ℝ in Ioi 0, gAlpha z |q - t| * Real.exp (-t)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change gAlpha alpha |(a - p * a) - a * t| * Real.exp (-t) =
      gAlpha z |q - t| * Real.exp (-t)
    have habs : |(a - p * a) - a * t| = a * |q - t| := by
      rw [show (a - p * a) - a * t = a * (q - t) by dsimp [q]; ring,
        abs_mul, abs_of_nonneg ha.le]
    rw [habs]
    have hg : gAlpha alpha (a * |q - t|) = gAlpha z |q - t| := by
      simp only [gAlpha]
      dsimp [z]
      congr 1 <;> ring_nf
    rw [hg]
  have hsecondChange :
      (∫ t : ℝ in Ioi 0,
        gAlpha alpha |(a - p * a) + (p * a) * t| * Real.exp (-t)) =
      (∫ t : ℝ in Ioi 0, gAlpha z |q + p * t| * Real.exp (-t)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change gAlpha alpha |(a - p * a) + (p * a) * t| * Real.exp (-t) =
      gAlpha z |q + p * t| * Real.exp (-t)
    have habs : |(a - p * a) + (p * a) * t| = a * |q + p * t| := by
      rw [show (a - p * a) + (p * a) * t = a * (q + p * t) by
        dsimp [q]; ring, abs_mul, abs_of_nonneg ha.le]
    rw [habs]
    have hg : gAlpha alpha (a * |q + p * t|) = gAlpha z |q + p * t| := by
      simp only [gAlpha]
      dsimp [z]
      congr 1 <;> ring_nf
    rw [hg]
  have hfirst := normalizedFirstRay_formula z q hz hq
  have hsecond := normalizedSecondRay_formula z p q hz hp hq
  change
    a / (a + p * a) *
        (∫ t : ℝ in Ioi 0,
          gAlpha alpha |(a - p * a) - a * t| * Real.exp (-t)) +
      p * a / (a + p * a) *
        (∫ t : ℝ in Ioi 0,
          gAlpha alpha |(a - p * a) + (p * a) * t| * Real.exp (-t)) =
    1 / (1 + p) *
      (Real.exp (-q) *
          ((1 + 2 * z) / (1 + z) ^ 2 +
            ∫ t : ℝ in Ioc 0 q, (1 + z * t) * Real.exp ((1 - z) * t)) +
        Real.exp (-z * q) *
          (p * (1 + z * q) / (1 + z * p) +
            z * p ^ 2 / (1 + z * p) ^ 2))
  rw [hweight1, hweight2, hfirstChange, hsecondChange, hfirst, hsecond]
  ring

/-- The value at the symmetric isotropic Laplace law. -/
def laplaceValue (alpha : ℝ) : ℝ :=
  2 * (1 + Real.sqrt 2 * alpha) / (Real.sqrt 2 + alpha) ^ 2

/-- The value at the shifted-exponential endpoint, with its removable value
at `alpha = 1` filled in. -/
def shiftedValue (alpha : ℝ) : ℝ :=
  if alpha = 1 then 9 / (4 * Real.exp 1)
  else
    (1 - alpha - alpha ^ 2) * Real.exp (-alpha) / (1 - alpha) ^ 2 +
      4 * alpha ^ 3 / (Real.exp 1 * (1 - alpha ^ 2) ^ 2)

/-- Splitting the shifted-exponential endpoint at its mode. -/
theorem asymLaplaceObjective_shifted_split (alpha : ℝ) (halpha : 0 ≤ alpha) :
    asymLaplaceObjective alpha 1 0 =
      Real.exp (-alpha) *
        (∫ t : ℝ in 0..1,
          (1 + alpha - alpha * t) * Real.exp (-(1 - alpha) * t)) +
      Real.exp (-1) * (1 + 2 * alpha) / (1 + alpha) ^ 2 := by
  have hint := integrableOn_shiftedIntegrand alpha halpha
  have htailInt : IntegrableOn
      (fun t : ℝ => gAlpha alpha |1 - t| * Real.exp (-t)) (Ioi 1) :=
    hint.mono_set (Ioi_subset_Ioi (by norm_num))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint htailInt
  have hfinite :
      (∫ t : ℝ in 0..1, gAlpha alpha |1 - t| * Real.exp (-t)) =
        Real.exp (-alpha) *
          (∫ t : ℝ in 0..1,
            (1 + alpha - alpha * t) * Real.exp (-(1 - alpha) * t)) := by
    calc
      _ = (∫ t : ℝ in 0..1,
          Real.exp (-alpha) *
            ((1 + alpha - alpha * t) *
              Real.exp (-(1 - alpha) * t))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) 1 := by
          simpa [uIcc] using ht
        have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht'.2
        change gAlpha alpha |1 - t| * Real.exp (-t) = _
        rw [abs_of_nonneg h1t]
        simp only [gAlpha]
        have hcoeff : 1 + alpha * (1 - t) =
            1 + alpha - alpha * t := by ring
        have hexp : Real.exp (-alpha * (1 - t)) * Real.exp (-t) =
            Real.exp (-alpha) * Real.exp (-(1 - alpha) * t) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [hcoeff, mul_assoc, hexp]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  have hlambda : 0 < 1 + alpha := by positivity
  have hbase := integral_linear_exp_Ioi
    (1 - alpha) alpha (1 + alpha) 1 hlambda (by
      intro t ht
      have hprod : 0 ≤ alpha * (t - 1) :=
        mul_nonneg halpha (sub_nonneg.mpr ht.le)
      nlinarith)
  have htail :
      (∫ t : ℝ in Ioi 1, gAlpha alpha |1 - t| * Real.exp (-t)) =
        Real.exp (-1) * (1 + 2 * alpha) / (1 + alpha) ^ 2 := by
    calc
      _ = (∫ t : ℝ in Ioi 1,
          Real.exp alpha *
            ((1 - alpha + alpha * t) *
              Real.exp (-(1 + alpha) * t))) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have h1t : 1 - t ≤ 0 := sub_nonpos.mpr ht.le
        change gAlpha alpha |1 - t| * Real.exp (-t) = _
        rw [abs_of_nonpos h1t]
        simp only [gAlpha]
        have hcoeff : 1 + alpha * (-(1 - t)) =
            1 - alpha + alpha * t := by ring
        have hexp : Real.exp (-alpha * (-(1 - t))) * Real.exp (-t) =
            Real.exp alpha * Real.exp (-(1 + alpha) * t) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [hcoeff, mul_assoc, hexp]
        ring
      _ = Real.exp alpha *
          (∫ t : ℝ in Ioi 1,
            (1 - alpha + alpha * t) *
              Real.exp (-(1 + alpha) * t)) := by
        rw [MeasureTheory.integral_const_mul]
      _ = Real.exp alpha *
          (Real.exp (-(1 + alpha) * 1) *
            ((1 - alpha) / (1 + alpha) + alpha * 1 / (1 + alpha) +
              alpha / (1 + alpha) ^ 2)) := by rw [hbase]
      _ = _ := by
        have hexp : Real.exp alpha * Real.exp (-(1 + alpha) * 1) =
            Real.exp (-1) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [show Real.exp alpha *
            (Real.exp (-(1 + alpha) * 1) *
              ((1 - alpha) / (1 + alpha) + alpha * 1 / (1 + alpha) +
                alpha / (1 + alpha) ^ 2)) =
            (Real.exp alpha * Real.exp (-(1 + alpha) * 1)) *
              ((1 - alpha) / (1 + alpha) + alpha * 1 / (1 + alpha) +
                alpha / (1 + alpha) ^ 2) by ring]
        rw [hexp]
        field_simp [hlambda.ne']
        ring
  have hobj : asymLaplaceObjective alpha 1 0 =
      (∫ t : ℝ in Ioi 0, gAlpha alpha |1 - t| * Real.exp (-t)) := by
    simp [asymLaplaceObjective]
  rw [hobj, ← hsplit, hfinite, htail]

/-- Exact evaluation at the shifted-exponential endpoint. -/
theorem asymLaplaceObjective_shifted (alpha : ℝ) (halpha : 0 ≤ alpha) :
    asymLaplaceObjective alpha 1 0 = shiftedValue alpha := by
  rw [asymLaplaceObjective_shifted_split alpha halpha]
  by_cases h : alpha = 1
  · subst alpha
    have hpoly : (∫ t : ℝ in 0..1, (2 - t)) = 3 / 2 := by
      have hc : IntervalIntegrable (fun _t : ℝ => (2 : ℝ)) volume 0 1 := by
        have hcont : Continuous (fun _t : ℝ => (2 : ℝ)) := by fun_prop
        exact hcont.intervalIntegrable 0 1
      have hi : IntervalIntegrable (fun t : ℝ => t) volume 0 1 := by
        have hcont : Continuous (fun t : ℝ => t) := by fun_prop
        exact hcont.intervalIntegrable 0 1
      rw [intervalIntegral.integral_sub hc hi]
      norm_num [integral_id]
    rw [show (∫ t : ℝ in 0..1,
        (1 + (1 : ℝ) - 1 * t) * Real.exp (-(1 - 1) * t)) = 3 / 2 by
      convert hpoly using 1
      all_goals norm_num]
    rw [show shiftedValue 1 = 9 / (4 * Real.exp 1) by simp [shiftedValue]]
    rw [show Real.exp (-1) = 1 / Real.exp 1 by
      rw [Real.exp_neg]
      simp [div_eq_mul_inv]]
    field_simp [Real.exp_ne_zero]
    ring
  · have hlambda : 1 - alpha ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have hplus : 1 + alpha ≠ 0 := by positivity
    have hI := intervalIntegral_linear_exp
      (1 + alpha) (-alpha) (1 - alpha) 0 1 hlambda
    have hI' :
        (∫ t : ℝ in 0..1,
          (1 + alpha - alpha * t) * Real.exp (-(1 - alpha) * t)) =
          -(Real.exp (-(1 - alpha) * 1) *
            ((1 + alpha) / (1 - alpha) + -alpha * 1 / (1 - alpha) +
              -alpha / (1 - alpha) ^ 2)) +
          Real.exp (-(1 - alpha) * 0) *
            ((1 + alpha) / (1 - alpha) + -alpha * 0 / (1 - alpha) +
              -alpha / (1 - alpha) ^ 2) := by
      simpa [sub_eq_add_neg] using hI
    have hexp : Real.exp (-alpha) * Real.exp (-(1 - alpha) * 1) =
        Real.exp (-1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hfinite :
        Real.exp (-alpha) *
          (∫ t : ℝ in 0..1,
            (1 + alpha - alpha * t) * Real.exp (-(1 - alpha) * t)) =
          Real.exp (-alpha) * (1 - alpha - alpha ^ 2) /
              (1 - alpha) ^ 2 -
            Real.exp (-1) * (1 - 2 * alpha) / (1 - alpha) ^ 2 := by
      calc
        _ = Real.exp (-alpha) *
            (-(Real.exp (-(1 - alpha) * 1) *
                ((1 + alpha) / (1 - alpha) + -alpha * 1 / (1 - alpha) +
                  -alpha / (1 - alpha) ^ 2)) +
              Real.exp (-(1 - alpha) * 0) *
                ((1 + alpha) / (1 - alpha) + -alpha * 0 / (1 - alpha) +
                  -alpha / (1 - alpha) ^ 2)) := by rw [hI']
        _ = -(Real.exp (-alpha) * Real.exp (-(1 - alpha) * 1)) *
                ((1 + alpha) / (1 - alpha) + -alpha * 1 / (1 - alpha) +
                  -alpha / (1 - alpha) ^ 2) +
              Real.exp (-alpha) *
                ((1 + alpha) / (1 - alpha) + -alpha * 0 / (1 - alpha) +
                  -alpha / (1 - alpha) ^ 2) := by
          rw [show Real.exp (-(1 - alpha) * 0) = 1 by simp]
          ring
        _ = _ := by
          rw [hexp]
          field_simp [hlambda]
          ring
    rw [hfinite]
    simp only [shiftedValue, if_neg h]
    have hfactor : 1 - alpha ^ 2 = (1 - alpha) * (1 + alpha) := by ring
    have hsquareDen : 1 - alpha ^ 2 ≠ 0 := by
      rw [hfactor]
      exact mul_ne_zero hlambda hplus
    have hexpneg : Real.exp (-1) = 1 / Real.exp 1 := by
      rw [Real.exp_neg]
      simp [div_eq_mul_inv]
    rw [hexpneg]
    field_simp [hlambda, hplus, hsquareDen, Real.exp_ne_zero]
    ring

/-- Exact evaluation at the symmetric endpoint. -/
theorem asymLaplaceObjective_symmetric (alpha : ℝ) (halpha : 0 ≤ alpha) :
    asymLaplaceObjective alpha (Real.sqrt 2 / 2) (Real.sqrt 2 / 2) =
      laplaceValue alpha := by
  let s : ℝ := Real.sqrt 2 / 2
  have hspos : 0 < s := by dsimp [s]; positivity
  have hs0 : s ≠ 0 := hspos.ne'
  have hlambda : 0 < 1 + alpha * s := by positivity
  have hI :
      (∫ t in Ioi (0 : ℝ),
        gAlpha alpha |s * t| * Real.exp (-t)) =
        1 / (1 + alpha * s) +
          alpha * s / (1 + alpha * s) ^ 2 := by
    calc
      _ = (∫ t in Ioi (0 : ℝ),
          (1 + alpha * s * t) * Real.exp (-(1 + alpha * s) * t)) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have ht0 : 0 ≤ t := ht.le
        change gAlpha alpha |s * t| * Real.exp (-t) =
          (1 + alpha * s * t) * Real.exp (-(1 + alpha * s) * t)
        rw [abs_of_nonneg (mul_nonneg hspos.le ht0)]
        simp only [gAlpha]
        rw [mul_assoc]
        rw [← Real.exp_add]
        congr 1 <;> ring_nf
      _ = Real.exp (-(1 + alpha * s) * 0) *
          (1 / (1 + alpha * s) + alpha * s * 0 / (1 + alpha * s) +
            alpha * s / (1 + alpha * s) ^ 2) := by
        apply integral_linear_exp_Ioi 1 (alpha * s) (1 + alpha * s) 0 hlambda
        intro t ht
        exact add_nonneg zero_le_one
          (mul_nonneg (mul_nonneg halpha hspos.le) ht.le)
      _ = _ := by simp
  have hsquare : s ^ 2 = 1 / 2 := by
    dsimp [s]
    have hsq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith
  change
    s / (s + s) *
        (∫ t in Ioi (0 : ℝ),
          gAlpha alpha |(s - s) - s * t| * Real.exp (-t)) +
      s / (s + s) *
        (∫ t in Ioi (0 : ℝ),
          gAlpha alpha |(s - s) + s * t| * Real.exp (-t)) =
      laplaceValue alpha
  have hminus :
      (∫ t in Ioi (0 : ℝ),
        gAlpha alpha |(s - s) - s * t| * Real.exp (-t)) =
      (∫ t in Ioi (0 : ℝ),
        gAlpha alpha |s * t| * Real.exp (-t)) := by
    simp only [sub_self, zero_sub, abs_neg]
  rw [hminus]
  simp only [sub_self, zero_add]
  rw [hI]
  dsimp [laplaceValue]
  have hsqrt : Real.sqrt (2 : ℝ) = 2 * s := by dsimp [s]; ring
  rw [hsqrt]
  field_simp [hs0, hlambda.ne']
  have hsquare_alpha : 2 * s ^ 2 * alpha ^ 2 = alpha ^ 2 := by
    rw [hsquare]
    ring
  have hden : (s * 2 + alpha) ^ 2 =
      2 * (1 + s * alpha) ^ 2 := by
    calc
      (s * 2 + alpha) ^ 2 =
          4 * s ^ 2 + 4 * s * alpha + alpha ^ 2 := by ring
      _ = 2 + 4 * s * alpha + alpha ^ 2 := by rw [hsquare]; ring
      _ = 2 + 4 * s * alpha + 2 * s ^ 2 * alpha ^ 2 := by
        rw [hsquare_alpha]
      _ = 2 * (1 + s * alpha) ^ 2 := by ring
  rw [hden]
  ring

open Set


/-!
# Elementary certificates for the asymmetric-Laplace calculation

This file contains the two analytic ingredients used in Claim (iii): the
alternating cubic/quartic bounds for `exp (-v)`, and the positivity
certificates for the two polynomial numerators.
-/

namespace AsymLaplaceCertificate

private lemma positive_of_positive_derivative
    {f f' : ℝ → ℝ} {v : ℝ} (hv : 0 < v) (h0 : f 0 = 0)
    (hcont : ContinuousOn f (Icc 0 v))
    (hder : ∀ x ∈ Ioo 0 v, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Ioo 0 v, 0 < f' x) :
    0 < f v := by
  obtain ⟨c, hc, hcder⟩ :=
    exists_hasDerivAt_eq_slope f f' hv hcont hder
  have hcpos := hpos c hc
  rw [hcder, h0] at hcpos
  have hcpos' : 0 < f v / v := by simpa using hcpos
  exact (div_pos_iff_of_pos_right hv).mp hcpos'

private lemma hasDerivAt_exp_neg (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (-y)) (-Real.exp (-x)) x := by
  change HasDerivAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) x
  exact mul_neg_one (Real.exp (-x)) ▸
    (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)

/-- The cubic alternating Taylor polynomial is a lower bound for `exp (-v)`.
The strict version is convenient in the positivity certificate. -/
theorem taylor₃_lt_exp_neg {v : ℝ} (hv : 0 < v) :
    1 - v + v ^ 2 / 2 - v ^ 3 / 6 < Real.exp (-v) := by
  have h₃ : ∀ {x : ℝ}, 0 < x → 0 < 1 - Real.exp (-x) := by
    intro x hx
    apply positive_of_positive_derivative hx (by simp)
    · fun_prop
    · intro y hy
      exact (hasDerivAt_exp_neg y).const_sub 1
    · intro y hy
      simpa only [neg_neg] using Real.exp_pos (-y)
  have h₂ : ∀ {x : ℝ}, 0 < x → 0 < Real.exp (-x) - 1 + x := by
    intro x hx
    apply positive_of_positive_derivative hx (by simp)
    · fun_prop
    · intro y hy
      exact ((hasDerivAt_exp_neg y).sub_const 1).add (hasDerivAt_id y)
    · intro y hy
      linarith [h₃ hy.1]
  have h₁ : ∀ {x : ℝ}, 0 < x →
      0 < 1 - x + x ^ 2 / 2 - Real.exp (-x) := by
    intro x hx
    apply positive_of_positive_derivative hx (by simp)
    · fun_prop
    · intro y hy
      exact ((((hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_id y)).add
        ((hasDerivAt_id y).pow 2 |>.div_const 2)).sub
          (hasDerivAt_exp_neg y))
    · intro y hy
      norm_num [pow_succ] at ⊢
      linarith [h₂ hy.1]
  apply sub_pos.mp
  have h₀ : 0 < Real.exp (-v) - (1 - v + v ^ 2 / 2 - v ^ 3 / 6) := by
    apply positive_of_positive_derivative hv (by simp)
    · fun_prop
    · intro x hx
      exact (hasDerivAt_exp_neg x).sub
        (((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
          ((hasDerivAt_id x).pow 2 |>.div_const 2)).sub
          ((hasDerivAt_id x).pow 3 |>.div_const 6)))
    · intro x hx
      norm_num [pow_succ] at ⊢
      linarith [h₁ hx.1]
  linarith

/-- The quartic alternating Taylor polynomial is an upper bound for
`exp (-v)`. -/
theorem exp_neg_lt_taylor₄ {v : ℝ} (hv : 0 < v) :
    Real.exp (-v) < 1 - v + v ^ 2 / 2 - v ^ 3 / 6 + v ^ 4 / 24 := by
  have h : 0 <
      (1 - v + v ^ 2 / 2 - v ^ 3 / 6 + v ^ 4 / 24) - Real.exp (-v) := by
    apply positive_of_positive_derivative hv (by norm_num)
    · fun_prop
    · intro x hx
      exact ((((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add
        ((hasDerivAt_id x).pow 2 |>.div_const 2)).sub
        ((hasDerivAt_id x).pow 3 |>.div_const 6)).add
        ((hasDerivAt_id x).pow 4 |>.div_const 24)).sub
        (hasDerivAt_exp_neg x))
    · intro x hx
      norm_num [pow_succ] at ⊢
      linarith [taylor₃_lt_exp_neg hx.1]
  linarith

/-! ## The rational recurrence and its polynomial certificates -/

/-- The abbreviation `c=1+p²` used in the calculation. -/
def c (p : ℝ) : ℝ := 1 + p ^ 2

/-- The rational coefficient multiplying `exp (-z(1-p))`. -/
def A (p z : ℝ) : ℝ :=
  (1 - z - z ^ 2 + z * (1 - z - z ^ 2) * p -
      z ^ 2 * (1 - z) * p ^ 2) /
    ((1 - z) ^ 2 * (1 + z * p) ^ 2)

/-- The rational coefficient multiplying `exp (p-1)`. -/
def B (p z : ℝ) : ℝ :=
  4 * z ^ 3 / ((1 + p) * (1 - z ^ 2) ^ 2)

/-- The differential operator `∂ₚ-(pz/c)∂_z`. -/
def L (F : ℝ → ℝ → ℝ) (p z : ℝ) : ℝ :=
  deriv (fun q ↦ F q z) p - p * z / c p * deriv (F p) z

/-- The common multiplier in the recurrence. -/
def M (p : ℝ) : ℝ := -(c p) ^ 2 / (2 * (1 - p ^ 2))

/-- One `C`-step in the recurrence from Claim (iii). -/
def Cstep (F : ℝ → ℝ → ℝ) (p z : ℝ) : ℝ :=
  M p * (L F p z + z * (1 + p) / c p * F p z)

/-- One `D`-step in the recurrence from Claim (iii). -/
def Dstep (F : ℝ → ℝ → ℝ) (p z : ℝ) : ℝ :=
  M p * (L F p z + F p z)

def C1num (p z : ℝ) : ℝ :=
  ((((((((((((1) * z + (-1)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * p + ((((((((-1) * z + (0)) * z + (-1)) * z + (0)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((1) * z + (-2)) * z + (1)) * z + (-2)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((-1) * z + (0)) * z + (-1)) * z + (0)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((-1) * z + (1)) * z + (-2)) * z + (0)) * z + (0)) * z + (0)))) * p + ((0)))

def C1den (p z : ℝ) : ℝ :=
  2 * (p - 1) * (z - 1) ^ 3 * (p * z + 1) ^ 3

def C1r (p z : ℝ) : ℝ := C1num p z / C1den p z

def D1num (p z : ℝ) : ℝ :=
  (((((((((((2) * z + (0)) * z + (-2)) * z + (0)) * z + (0)) * z + (0)) * p + (((((((2) * z + (0)) * z + (6)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((6) * z + (0)) * z + (2)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((2) * z + (0)) * z + (6)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((4) * z + (0)) * z + (4)) * z + (0)) * z + (0)) * z + (0)))) * p + ((0)))

def D1den (p z : ℝ) : ℝ :=
  (p - 1) * (p + 1) ^ 3 * (z - 1) ^ 3 * (z + 1) ^ 3

def D1r (p z : ℝ) : ℝ := D1num p z / D1den p z

def C2num (p z : ℝ) : ℝ :=
  (((((((((((((((((((1) * z + (-1)) * z + (1)) * z + (-1)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * p + (((((((((((-2) * z + (1)) * z + (-4)) * z + (1)) * z + (-2)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((3) * z + (-3)) * z + (10)) * z + (-8)) * z + (1)) * z + (-3)) * z + (0)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((-4) * z + (3)) * z + (-12)) * z + (8)) * z + (-2)) * z + (3)) * z + (-2)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((3) * z + (-3)) * z + (18)) * z + (-14)) * z + (3)) * z + (-9)) * z + (2)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((-2) * z + (3)) * z + (-12)) * z + (14)) * z + (0)) * z + (9)) * z + (-6)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((1) * z + (-1)) * z + (10)) * z + (-8)) * z + (3)) * z + (-9)) * z + (4)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((((1) * z + (-4)) * z + (8)) * z + (-2)) * z + (9)) * z + (-6)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((1) * z + (-1)) * z + (1)) * z + (-3)) * z + (2)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((1) * z + (-2)) * z + (3)) * z + (-2)) * z + (0)) * z + (0)) * z + (0))))

def C2den (p z : ℝ) : ℝ :=
  4 * (p - 1) ^ 3 * (z - 1) ^ 4 * (p * z + 1) ^ 4

def C2r (p z : ℝ) : ℝ := C2num p z / C2den p z

def D2num (p z : ℝ) : ℝ :=
  (((((((((((((((((((1) * z + (0)) * z + (-2)) * z + (0)) * z + (1)) * z + (0)) * z + (0)) * z + (0)) * p + (((((((((3) * z + (0)) * z + (2)) * z + (0)) * z + (-5)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((7) * z + (0)) * z + (6)) * z + (0)) * z + (11)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((1) * z + (0)) * z + (34)) * z + (0)) * z + (-11)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((9) * z + (0)) * z + (-10)) * z + (0)) * z + (25)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((-23) * z + (0)) * z + (54)) * z + (0)) * z + (-7)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((1) * z + (0)) * z + (-50)) * z + (0)) * z + (25)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((-39) * z + (0)) * z + (14)) * z + (0)) * z + (1)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((-2) * z + (0)) * z + (-36)) * z + (0)) * z + (14)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((-20) * z + (0)) * z + (-8)) * z + (0)) * z + (4)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((-4) * z + (0)) * z + (4)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((-2) * z + (0)) * z + (0)) * z + (0)) * z + (2)) * z + (0)) * z + (0)) * z + (0))))

def D2den (p z : ℝ) : ℝ :=
  (p - 1) ^ 3 * (p + 1) ^ 5 * (z - 1) ^ 4 * (z + 1) ^ 4

def D2r (p z : ℝ) : ℝ := D2num p z / D2den p z

set_option maxHeartbeats 1000000 in
def C3num (p z : ℝ) : ℝ :=
  ((((((((((((((((((((((((((1) * z + (-1)) * z + (3)) * z + (-1)) * z + (-2)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * p + ((((((((((((((-3) * z + (1)) * z + (-11)) * z + (-3)) * z + (2)) * z + (-10)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((((((((6) * z + (-3)) * z + (33)) * z + (1)) * z + (-3)) * z + (12)) * z + (-22)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((((((((-10) * z + (4)) * z + (-57)) * z + (-15)) * z + (25)) * z + (-21)) * z + (52)) * z + (-26)) * z + (0)) * z + (0)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((((((((12) * z + (-4)) * z + (92)) * z + (13)) * z + (-16)) * z + (20)) * z + (-118)) * z + (65)) * z + (-16)) * z + (0)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((((((((-12) * z + (6)) * z + (-108)) * z + (-30)) * z + (60)) * z + (6)) * z + (208)) * z + (-150)) * z + (24)) * z + (-4)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((((((((10) * z + (-4)) * z + (108)) * z + (22)) * z + (-52)) * z + (0)) * z + (-274)) * z + (260)) * z + (-72)) * z + (2)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((((((((-6) * z + (4)) * z + (-92)) * z + (-30)) * z + (52)) * z + (34)) * z + (334)) * z + (-320)) * z + (88)) * z + (-16)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((((((((3) * z + (-3)) * z + (57)) * z + (13)) * z + (-60)) * z + (0)) * z + (-334)) * z + (390)) * z + (-120)) * z + (6)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((((((((-1) * z + (1)) * z + (-33)) * z + (-15)) * z + (16)) * z + (6)) * z + (274)) * z + (-320)) * z + (120)) * z + (-24)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((((-1) * z + (11)) * z + (1)) * z + (-25)) * z + (20)) * z + (-208)) * z + (260)) * z + (-88)) * z + (6)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((((((-3) * z + (-3)) * z + (3)) * z + (-21)) * z + (118)) * z + (-150)) * z + (72)) * z + (-16)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((-1) * z + (-2)) * z + (12)) * z + (-52)) * z + (65)) * z + (-24)) * z + (2)) * z + (0)) * z + (0)) * z + (0)))) * p + ((((((((((2) * z + (-10)) * z + (22)) * z + (-26)) * z + (16)) * z + (-4)) * z + (0)) * z + (0)) * z + (0))))

def C3den (p z : ℝ) : ℝ :=
  8 * (p - 1) ^ 5 * (z - 1) ^ 5 * (p * z + 1) ^ 5

def C3r (p z : ℝ) : ℝ := C3num p z / C3den p z

set_option maxHeartbeats 1000000 in
def D3num (p z : ℝ) : ℝ :=
  (((((((((((((((((((((((((((1) * z + (0)) * z + (-3)) * z + (0)) * z + (3)) * z + (0)) * z + (-1)) * z + (0)) * z + (0)) * z + (0)) * p + (((((((((((7) * z + (0)) * z + (-9)) * z + (0)) * z + (-3)) * z + (0)) * z + (5)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((19) * z + (0)) * z + (15)) * z + (0)) * z + (-15)) * z + (0)) * z + (-19)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((19) * z + (0)) * z + (111)) * z + (0)) * z + (9)) * z + (0)) * z + (53)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((16) * z + (0)) * z + (84)) * z + (0)) * z + (216)) * z + (0)) * z + (-124)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((-80) * z + (0)) * z + (288)) * z + (0)) * z + (-264)) * z + (0)) * z + (248)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((8) * z + (0)) * z + (-540)) * z + (0)) * z + (1056)) * z + (0)) * z + (-332)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((-322) * z + (0)) * z + (546)) * z + (0)) * z + (-1206)) * z + (0)) * z + (598)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((335) * z + (0)) * z + (-2085)) * z + (0)) * z + (1797)) * z + (0)) * z + (-431)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((-415) * z + (0)) * z + (1305)) * z + (0)) * z + (-2085)) * z + (0)) * z + (811)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((911) * z + (0)) * z + (-2493)) * z + (0)) * z + (1461)) * z + (0)) * z + (-263)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((-253) * z + (0)) * z + (1671)) * z + (0)) * z + (-1863)) * z + (0)) * z + (637)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((934) * z + (0)) * z + (-1230)) * z + (0)) * z + (522)) * z + (0)) * z + (-34)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((-86) * z + (0)) * z + (906)) * z + (0)) * z + (-906)) * z + (0)) * z + (278)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((406) * z + (0)) * z + (-246)) * z + (0)) * z + (-6)) * z + (0)) * z + (38)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((-20) * z + (0)) * z + (168)) * z + (0)) * z + (-204)) * z + (0)) * z + (56)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((58) * z + (0)) * z + (-30)) * z + (0)) * z + (-42)) * z + (0)) * z + (14)) * z + (0)) * z + (0)) * z + (0)))) * p + (((((((((((-2) * z + (0)) * z + (6)) * z + (0)) * z + (-6)) * z + (0)) * z + (2)) * z + (0)) * z + (0)) * z + (0))))

def D3den (p z : ℝ) : ℝ :=
  2 * (p - 1) ^ 5 * (p + 1) ^ 7 * (z - 1) ^ 5 * (z + 1) ^ 5

def D3r (p z : ℝ) : ℝ := D3num p z / D3den p z

/-- Explicit rational normal forms of the three recurrence iterates. -/
def C₁ : ℝ → ℝ → ℝ := C1r
def C₂ : ℝ → ℝ → ℝ := C2r
def C₃ : ℝ → ℝ → ℝ := C3r
def D₁ : ℝ → ℝ → ℝ := D1r
def D₂ : ℝ → ℝ → ℝ := D2r
def D₃ : ℝ → ℝ → ℝ := D3r

/-! The next six identities kernel-check that the displayed rational
normal forms are exactly the successive iterates of the recurrence. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Cstep_A_eq_C₁ {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) : Cstep A p z = C₁ p z := by
  have hpz : 1 + z * p ≠ 0 := by positivity
  have hz : 1 - z ≠ 0 := by linarith
  have hp : 1 - p ^ 2 ≠ 0 := by nlinarith
  have hpm : p - 1 ≠ 0 := by linarith
  have hzm : z - 1 ≠ 0 := by linarith
  unfold Cstep L M c A C₁ C1r
  rw [deriv_fun_div
    (c := fun q : ℝ =>
      1 - z - z ^ 2 + z * (1 - z - z ^ 2) * q -
        z ^ 2 * (1 - z) * q ^ 2)
    (d := fun q : ℝ => (1 - z) ^ 2 * (1 + z * q) ^ 2)
    (by fun_prop) (by fun_prop)
    (mul_ne_zero (pow_ne_zero 2 hz) (pow_ne_zero 2 hpz))]
  rw [deriv_fun_div
    (c := fun w : ℝ =>
      1 - w - w ^ 2 + w * (1 - w - w ^ 2) * p -
        w ^ 2 * (1 - w) * p ^ 2)
    (d := fun w : ℝ => (1 - w) ^ 2 * (1 + w * p) ^ 2)
    (by fun_prop) (by fun_prop)
    (mul_ne_zero (pow_ne_zero 2 hz) (pow_ne_zero 2 hpz))]
  simp (disch := fun_prop) [C1num, C1den]
  field_simp [hpz, hz, hp, hpm, hzm]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem Dstep_B_eq_D₁ {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) : Dstep B p z = D₁ p z := by
  have hpp : 1 + p ≠ 0 := by positivity
  have hzp : z + 1 ≠ 0 := by positivity
  have hzm : z - 1 ≠ 0 := by linarith
  have hz2 : 1 - z ^ 2 ≠ 0 := by nlinarith
  have hp2 : 1 - p ^ 2 ≠ 0 := by nlinarith
  have hpm : p - 1 ≠ 0 := by linarith
  unfold Dstep L M c B D₁ D1r
  rw [deriv_fun_div
    (c := fun _ : ℝ => 4 * z ^ 3)
    (d := fun q : ℝ => (1 + q) * (1 - z ^ 2) ^ 2)
    (by fun_prop) (by fun_prop) (mul_ne_zero hpp (pow_ne_zero 2 hz2))]
  rw [deriv_fun_div
    (c := fun w : ℝ => 4 * w ^ 3)
    (d := fun w : ℝ => (1 + p) * (1 - w ^ 2) ^ 2)
    (by fun_prop) (by fun_prop) (mul_ne_zero hpp (pow_ne_zero 2 hz2))]
  simp (disch := fun_prop) [D1num, D1den]
  field_simp [hpp, hzp, hzm, hz2, hp2, hpm]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem Cstep_C₁_eq_C₂ {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) : Cstep C₁ p z = C₂ p z := by
  have hpz : p * z + 1 ≠ 0 := by positivity
  have hp : 1 - p ^ 2 ≠ 0 := by nlinarith
  have hpm : p - 1 ≠ 0 := by linarith
  have hzm : z - 1 ≠ 0 := by linarith
  have hden : C1den p z ≠ 0 := by
    unfold C1den
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) hpm) (pow_ne_zero 3 hzm))
      (pow_ne_zero 3 hpz)
  unfold Cstep L M c C₁ C1r C₂ C2r
  rw [deriv_fun_div
    (c := fun q : ℝ => C1num q z)
    (d := fun q : ℝ => C1den q z)
    (by unfold C1num; fun_prop) (by unfold C1den; fun_prop) hden]
  rw [deriv_fun_div
    (c := fun w : ℝ => C1num p w)
    (d := fun w : ℝ => C1den p w)
    (by unfold C1num; fun_prop) (by unfold C1den; fun_prop) hden]
  simp (disch := fun_prop) [C1num, C1den, C2num, C2den]
  field_simp [hpz, hp, hpm, hzm]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem Dstep_D₁_eq_D₂ {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) : Dstep D₁ p z = D₂ p z := by
  have hpp : p + 1 ≠ 0 := by positivity
  have hzp : z + 1 ≠ 0 := by positivity
  have hzm : z - 1 ≠ 0 := by linarith
  have hp2 : 1 - p ^ 2 ≠ 0 := by nlinarith
  have hpm : p - 1 ≠ 0 := by linarith
  have hden : D1den p z ≠ 0 := by
    unfold D1den
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero hpm (pow_ne_zero 3 hpp))
        (pow_ne_zero 3 hzm)) (pow_ne_zero 3 hzp)
  unfold Dstep L M c D₁ D1r D₂ D2r
  rw [deriv_fun_div
    (c := fun q : ℝ => D1num q z)
    (d := fun q : ℝ => D1den q z)
    (by unfold D1num; fun_prop) (by unfold D1den; fun_prop) hden]
  rw [deriv_fun_div
    (c := fun w : ℝ => D1num p w)
    (d := fun w : ℝ => D1den p w)
    (by unfold D1num; fun_prop) (by unfold D1den; fun_prop) hden]
  simp (disch := fun_prop) [D1num, D1den, D2num, D2den]
  field_simp [hpp, hzp, hzm, hp2, hpm]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem Cstep_C₂_eq_C₃ {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) : Cstep C₂ p z = C₃ p z := by
  have hpz : p * z + 1 ≠ 0 := by positivity
  have hp2 : 1 - p ^ 2 ≠ 0 := by nlinarith
  have hpm : p - 1 ≠ 0 := by linarith
  have hzm : z - 1 ≠ 0 := by linarith
  have hden : C2den p z ≠ 0 := by
    unfold C2den
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hpm))
        (pow_ne_zero 4 hzm)) (pow_ne_zero 4 hpz)
  unfold Cstep L M c C₂ C2r C₃ C3r
  rw [deriv_fun_div
    (c := fun q : ℝ => C2num q z)
    (d := fun q : ℝ => C2den q z)
    (by unfold C2num; fun_prop) (by unfold C2den; fun_prop) hden]
  rw [deriv_fun_div
    (c := fun w : ℝ => C2num p w)
    (d := fun w : ℝ => C2den p w)
    (by unfold C2num; fun_prop) (by unfold C2den; fun_prop) hden]
  simp (disch := fun_prop) [C2num, C2den, C3num, C3den]
  field_simp [hpz, hp2, hpm, hzm]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem Dstep_D₂_eq_D₃ {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) : Dstep D₂ p z = D₃ p z := by
  have hpp : p + 1 ≠ 0 := by positivity
  have hzp : z + 1 ≠ 0 := by positivity
  have hzm : z - 1 ≠ 0 := by linarith
  have hp2 : 1 - p ^ 2 ≠ 0 := by nlinarith
  have hpm : p - 1 ≠ 0 := by linarith
  have hden : D2den p z ≠ 0 := by
    unfold D2den
    exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 3 hpm) (pow_ne_zero 5 hpp))
        (pow_ne_zero 4 hzm)) (pow_ne_zero 4 hzp)
  unfold Dstep L M c D₂ D2r D₃ D3r
  rw [deriv_fun_div
    (c := fun q : ℝ => D2num q z)
    (d := fun q : ℝ => D2den q z)
    (by unfold D2num; fun_prop) (by unfold D2den; fun_prop) hden]
  rw [deriv_fun_div
    (c := fun w : ℝ => D2num p w)
    (d := fun w : ℝ => D2den p w)
    (by unfold D2num; fun_prop) (by unfold D2den; fun_prop) hden]
  simp (disch := fun_prop) [D2num, D2den, D3num, D3den]
  field_simp [hpp, hzp, hzm, hp2, hpm]
  ring

/-- The Taylor argument `v=(1-p)(1-z)`. -/
def v (p z : ℝ) : ℝ := (1 - p) * (1 - z)

def T₃ (p z : ℝ) : ℝ :=
  1 - v p z + (v p z) ^ 2 / 2 - (v p z) ^ 3 / 6

def T₄ (p z : ℝ) : ℝ := T₃ p z + (v p z) ^ 4 / 24

def Q₃ (p z : ℝ) : ℝ :=
  (((((((((((((((((((((((((2) * z + 2) * z + (-4)) * z + (-4)) * z + 2) * z + 2) * z + 0) * z + 0) * z + 0) * z + 0) * z + 0) * p + (((((((((((16) * z + 20) * z + (-10)) * z + (-28)) * z + (-16)) * z + 8) * z + 10) * z + 0) * z + 0) * z + 0) * z + 0)) * p + (((((((((((48) * z + 74) * z + 46) * z + (-44)) * z + (-56)) * z + (-2)) * z + 10) * z + 20) * z + 0) * z + 0) * z + 0)) * p + (((((((((((44) * z + 86) * z + 198) * z + 116) * z + 32) * z + (-10)) * z + 90) * z + 0) * z + 20) * z + 0) * z + 0)) * p + ((((((((((((-26)) * z + (-136)) * z + (-118)) * z + 300) * z + 544) * z + 394) * z + 90) * z + 200) * z + (-10)) * z + 10) * z + 0)) * p + ((((((((((((-219)) * z + (-622)) * z + (-842)) * z + (-374)) * z + 201) * z + 1436) * z + 902) * z + 96) * z + 196) * z + (-8)) * z + 2)) * p + ((((((((((((-112)) * z + (-958)) * z + (-2172)) * z + (-1576)) * z + 50) * z + 240) * z + 1960) * z + 1120) * z + 12) * z + 94) * z + (-2))) * p + ((((((((((((-251)) * z + (-583)) * z + (-1324)) * z + (-3684)) * z + (-1649)) * z + 1651) * z + 882) * z + 1442) * z + 836) * z + (-26)) * z + 18)) * p + (((((((((((108) * z + (-649)) * z + (-1175)) * z + (-818)) * z + (-3402)) * z + (-517)) * z + 2903) * z + 1320) * z + 544) * z + 352) * z + (-10))) * p + ((((((((((((-25)) * z + 374) * z + (-981)) * z + (-1945)) * z + (-100)) * z + (-456)) * z + 847) * z + 1993) * z + 915) * z + 82) * z + 64)) * p + (((((((((((28) * z + (-184)) * z + (-70)) * z + (-1107)) * z + (-1445)) * z + 652) * z + 1638) * z + 863) * z + 545) * z + 328) * z + 0)) * p + (((((((((((3) * z + 77) * z + (-410)) * z + (-236)) * z + 171) * z + (-457)) * z + (-148)) * z + 954) * z + 478) * z + 94) * z + 50)) * p + (((((((((((0) * z + 3) * z + 133) * z + 18) * z + 252) * z + 193) * z + (-629)) * z + (-380)) * z + 294) * z + 190) * z + 22)) * p + (((((((((((0) * z + 0) * z + 9) * z + 163) * z + 59) * z + (-268)) * z + (-271)) * z + 11) * z + 185) * z + 94) * z + 18)) * p + (((((((((((0) * z + 0) * z + 0) * z + 3) * z + (-13)) * z + (-158)) * z + (-200)) * z + 37) * z + 187) * z + 118) * z + 26)) * p + (((((((((((0) * z + 0) * z + 0) * z + 0) * z + (-6)) * z + (-20)) * z + (-20)) * z + 4) * z + 22) * z + 16) * z + 4)

def Q₄ (p z : ℝ) : ℝ :=
  ((((((((((((((((((((((((((1) * z + 1) * z + (-2)) * z + (-2)) * z + 1) * z + 1) * z + 0) * z + 0) * z + 0) * z + 0) * z + 0) * p + (((((((((((7) * z + 8) * z + (-5)) * z + (-12)) * z + (-7)) * z + 4) * z + 5) * z + 0) * z + 0) * z + 0) * z + 0)) * p + (((((((((((16) * z + 19) * z + 13) * z + (-12)) * z + (-10)) * z + 7) * z + 5) * z + 10) * z + 0) * z + 0) * z + 0)) * p + ((((((((((((-2)) * z + (-18)) * z + 42) * z + 80) * z + 96) * z + 58) * z + 70) * z + 0) * z + 10) * z + 0) * z + 0)) * p + ((((((((((((-35)) * z + (-133)) * z + (-124)) * z + 240) * z + 532) * z + 468) * z + 160) * z + 140) * z + (-5)) * z + 5) * z + 0)) * p + ((((((((((((-95)) * z + (-218)) * z + (-65)) * z + 436) * z + 942) * z + 1490) * z + 956) * z + 168) * z + 133) * z + (-4)) * z + 1)) * p + (((((((((((64) * z + 27) * z + 249) * z + 1418) * z + 2744) * z + 2184) * z + 2158) * z + 1120) * z + 78) * z + 63) * z + (-1))) * p + ((((((((((((-38)) * z + 506) * z + 1910) * z + 2544) * z + 4366) * z + 5932) * z + 3174) * z + 1748) * z + 788) * z + 10) * z + 12)) * p + (((((((((((232) * z + 544) * z + 2194) * z + 6082) * z + 6675) * z + 7331) * z + 7010) * z + 2904) * z + 775) * z + 311) * z + (-2))) * p + ((((((((((((-14)) * z + 930) * z + 1998) * z + 4208) * z + 9563) * z + 10212) * z + 7501) * z + 4576) * z + 1611) * z + 162) * z + 53)) * p + (((((((((((58) * z + 38) * z + 1580) * z + 3912) * z + 6520) * z + 10075) * z + 8841) * z + 3998) * z + 1412) * z + 493) * z + 9)) * p + ((((((((((((-2)) * z + 232) * z + 466) * z + 2776) * z + 6294) * z + 7478) * z + 6506) * z + 3828) * z + 952) * z + 110) * z + 64)) * p + (((((((((((0) * z + (-16)) * z + 410) * z + 1120) * z + 2452) * z + 3542) * z + 3256) * z + 2140) * z + 972) * z + 186) * z + (-22))) * p + (((((((((((0) * z + 0) * z + (-26)) * z + 288) * z + 242) * z + (-330)) * z + (-26)) * z + 656) * z + 506) * z + 178) * z + 48)) * p + (((((((((((0) * z + 0) * z + 0) * z + (-38)) * z + (-74)) * z + (-146)) * z + 240) * z + 872) * z + 640) * z + 104) * z + (-14))) * p + (((((((((((0) * z + 0) * z + 0) * z + 0) * z + (-16)) * z + 68) * z + 414) * z + 784) * z + 680) * z + 264) * z + 38)) * p + (((((((((((0) * z + 0) * z + 0) * z + 0) * z + 0) * z + 10) * z + 50) * z + 96) * z + 88) * z + 38) * z + 6)

private def N₃ (p z : ℝ) : ℝ :=
  C3num p z * (p + 1) ^ 7 * (z + 1) ^ 5 +
    4 * T₃ p z * D3num p z * (p * z + 1) ^ 5

private def N₄ (p z : ℝ) : ℝ :=
  C3num p z * (p + 1) ^ 7 * (z + 1) ^ 5 +
    4 * T₄ p z * D3num p z * (p * z + 1) ^ 5

private def W (p z : ℝ) : ℝ :=
  8 * (p - 1) ^ 5 * (p + 1) ^ 7 * (z - 1) ^ 5 *
    (z + 1) ^ 5 * (p * z + 1) ^ 5

private theorem C₃_T₃_D₃_common {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    C₃ p z + T₃ p z * D₃ p z = N₃ p z / W p z := by
  have hpz : p * z + 1 ≠ 0 := by positivity
  have hpp : p + 1 ≠ 0 := by positivity
  have hzp : z + 1 ≠ 0 := by positivity
  have hpm : p - 1 ≠ 0 := by linarith
  have hzm : z - 1 ≠ 0 := by linarith
  unfold C₃ C3r D₃ D3r C3den D3den N₃ W
  field_simp [hpz, hpp, hzp, hpm, hzm]
  ring

private theorem C₃_T₄_D₃_common {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    C₃ p z + T₄ p z * D₃ p z = N₄ p z / W p z := by
  have hpz : p * z + 1 ≠ 0 := by positivity
  have hpp : p + 1 ≠ 0 := by positivity
  have hzp : z + 1 ≠ 0 := by positivity
  have hpm : p - 1 ≠ 0 := by linarith
  have hzm : z - 1 ≠ 0 := by linarith
  unfold C₃ C3r D₃ D3r C3den D3den N₄ W
  field_simp [hpz, hpp, hzp, hpm, hzm]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem N₃_eq_Q₃ (p z : ℝ) :
    N₃ p z =
      -(z ^ 3 * (c p) ^ 3 * Q₃ p z * (1 - p) ^ 4 * (1 - z) ^ 4) / 3 := by
  unfold N₃ C3num D3num T₃ v c Q₃
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem N₄_eq_Q₄ (p z : ℝ) :
    N₄ p z =
      -(z ^ 3 * (c p) ^ 3 * Q₄ p z * (1 - p) ^ 4 * (1 - z) ^ 5) / 6 := by
  unfold N₄ C3num D3num T₄ T₃ v c Q₄
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Exact cubic Taylor-bracket identity produced by the recurrence. -/
theorem C₃_add_T₃_mul_D₃_eq_Q₃ {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    C₃ p z + T₃ p z * D₃ p z =
      -(z ^ 3 * (c p) ^ 3 * Q₃ p z) /
        (24 * (1 - p) * (1 + p) ^ 7 * (1 - z) *
          (1 + z) ^ 5 * (1 + p * z) ^ 5) := by
  rw [C₃_T₃_D₃_common hp₀ hp₁ hz₀ hz₁, N₃_eq_Q₃]
  have hpz : 1 + p * z ≠ 0 := by positivity
  have hpp : 1 + p ≠ 0 := by positivity
  have hzp : 1 + z ≠ 0 := by positivity
  have hpm : 1 - p ≠ 0 := by linarith
  have hzm : 1 - z ≠ 0 := by linarith
  have hpz' : p * z + 1 ≠ 0 := by positivity
  have hpp' : p + 1 ≠ 0 := by positivity
  have hzp' : z + 1 ≠ 0 := by positivity
  have hpm' : p - 1 ≠ 0 := by linarith
  have hzm' : z - 1 ≠ 0 := by linarith
  unfold W
  field_simp [hpz, hpp, hzp, hpm, hzm, hpz', hpp', hzp', hpm', hzm']
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Exact quartic Taylor-bracket identity produced by the recurrence. -/
theorem C₃_add_T₄_mul_D₃_eq_Q₄ {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) :
    C₃ p z + T₄ p z * D₃ p z =
      -(z ^ 3 * (c p) ^ 3 * Q₄ p z) /
        (48 * (1 - p) * (1 + p) ^ 7 *
          (1 + z) ^ 5 * (1 + p * z) ^ 5) := by
  rw [C₃_T₄_D₃_common hp₀ hp₁ hz₀ hz₁, N₄_eq_Q₄]
  have hpz : 1 + p * z ≠ 0 := by positivity
  have hpp : 1 + p ≠ 0 := by positivity
  have hzp : 1 + z ≠ 0 := by positivity
  have hpm : 1 - p ≠ 0 := by linarith
  have hpz' : p * z + 1 ≠ 0 := by positivity
  have hpp' : p + 1 ≠ 0 := by positivity
  have hzp' : z + 1 ≠ 0 := by positivity
  have hpm' : p - 1 ≠ 0 := by linarith
  have hzm' : z - 1 ≠ 0 := by linarith
  unfold W
  field_simp [hpz, hpp, hzp, hpm, hpz', hpp', hzp', hpm', hzm']
  ring

def P₃ (x y : ℝ) : ℝ :=
  (((((((((((((((((((((((((0) * y + 98304) * y + 417792) * y + 798720) * y + 903168) * y + 666624) * y + 333312) * y + 112896) * y + 24960) * y + 3264) * y + 192) * x + (((((((((((0) * y + 767616) * y + 3378688) * y + 6705376) * y + 7891744) * y + 6074656) * y + 3168160) * y + 1116940) * y + 256036) * y + 34564) * y + 2092)) * x + (((((((((((24576) * y + 2872896) * y + 12925024) * y + 26640768) * y + 32739872) * y + 26362912) * y + 14363556) * y + 5269064) * y + 1249972) * y + 173712) * y + 10784)) * x + (((((((((((147456) * y + 6820224) * y + 31159936) * y + 66889376) * y + 86174704) * y + 72766060) * y + 41423252) * y + 15782518) * y + 3863206) * y + 550796) * y + 34948)) * x + (((((((((((393216) * y + 11419296) * y + 53228672) * y + 119712344) * y + 162311276) * y + 143820744) * y + 85365798) * y + 33660276) * y + 8467432) * y + 1233760) * y + 79720)) * x + (((((((((((614400) * y + 14239560) * y + 68817224) * y + 163424682) * y + 233635930) * y + 216703494) * y + 133482186) * y + 54187539) * y + 13943227) * y + 2068140) * y + 135626)) * x + (((((((((((623616) * y + 13740036) * y + 70437170) * y + 177602890) * y + 267001328) * y + 257591976) * y + 163502355) * y + 67914195) * y + 17789917) * y + 2676602) * y + 177634)) * x + (((((((((((430080) * y + 10636476) * y + 58973230) * y + 157528528) * y + 246874684) * y + 245365519) * y + 159167632) * y + 67225642) * y + 17848678) * y + 2716102) * y + 182026)) * x + (((((((((((204288) * y + 6837996) * y + 41124274) * y + 114921738) * y + 185262269) * y + 187638085) * y + 123405162) * y + 52705922) * y + 14133298) * y + 2170602) * y + 146690)) * x + (((((((((((66048) * y + 3722616) * y + 23822548) * y + 68324258) * y + 111708487) * y + 114174061) * y + 75630470) * y + 32524612) * y + 8785636) * y + 1359818) * y + 92596)) * x + (((((((((((13920) * y + 1693944) * y + 11181480) * y + 32318088) * y + 52989198) * y + 54265837) * y + 36041842) * y + 15562264) * y + 4227398) * y + 658832) * y + 45188)) * x + (((((((((((1728) * y + 614292) * y + 4073466) * y + 11723112) * y + 19146828) * y + 19568755) * y + 12999930) * y + 5627420) * y + 1535906) * y + 240918) * y + 16642)) * x + (((((((((((96) * y + 165348) * y + 1086294) * y + 3097170) * y + 5026551) * y + 5120689) * y + 3400466) * y + 1475278) * y + 404486) * y + 63850) * y + 4442)) * x + (((((((((((0) * y + 30096) * y + 195260) * y + 551540) * y + 890003) * y + 904431) * y + 600840) * y + 261429) * y + 72037) * y + 11446) * y + 802)) * x + (((((((((((0) * y + 3204) * y + 20582) * y + 57750) * y + 92860) * y + 94311) * y + 62787) * y + 27441) * y + 7609) * y + 1218) * y + 86)) * x + (((((((((((0) * y + 144) * y + 920) * y + 2572) * y + 4130) * y + 4200) * y + 2808) * y + 1236) * y + 346) * y + 56) * y + 4)

def P₄ (x y : ℝ) : ℝ :=
  ((((((((((((((((((((((((((196608) * y + 983040) * y + 2211840) * y + 2949120) * y + 2580480) * y + 1548288) * y + 645120) * y + 184320) * y + 34560) * y + 3840) * y + 192) * x + (((((((((((1805568) * y + 9152768) * y + 20948416) * y + 28506112) * y + 25535104) * y + 15722368) * y + 6728920) * y + 1972576) * y + 378256) * y + 42784) * y + 2168)) * x + (((((((((((7760256) * y + 40066624) * y + 93712768) * y + 130768704) * y + 120492032) * y + 76457608) * y + 33721008) * y + 10161752) * y + 1993720) * y + 229344) * y + 11752)) * x + (((((((((((20762496) * y + 109811008) * y + 264027648) * y + 380068960) * y + 362205240) * y + 237900552) * y + 108432364) * y + 33633840) * y + 6752412) * y + 789328) * y + 40832)) * x + (((((((((((38862912) * y + 212048448) * y + 527884272) * y + 789101224) * y + 781878432) * y + 533331868) * y + 251570504) * y + 80326672) * y + 16492940) * y + 1957896) * y + 102164)) * x + (((((((((((54349776) * y + 308494688) * y + 801261716) * y + 1251161232) * y + 1293357320) * y + 917069628) * y + 447310662) * y + 146802868) * y + 30787858) * y + 3709800) * y + 195295)) * x + (((((((((((59398296) * y + 353743244) * y + 964652508) * y + 1578371324) * y + 1702168576) * y + 1251791886) * y + 629360694) * y + 211679260) * y + 45261618) * y + 5533777) * y + 294173)) * x + (((((((((((52516224) * y + 330197184) * y + 947503092) * y + 1621952204) * y + 1817248870) * y + 1378917268) * y + 711122632) * y + 244208676) * y + 53126696) * y + 6588738) * y + 354170)) * x + (((((((((((38552400) * y + 255999376) * y + 769929172) * y + 1369801686) * y + 1582690466) * y + 1230691180) * y + 647478780) * y + 226175726) * y + 49961314) * y + 6283812) * y + 342034)) * x + (((((((((((23812968) * y + 165726676) * y + 517332492) * y + 947193568) * y + 1118862840) * y + 885475752) * y + 472888459) * y + 167486088) * y + 37504866) * y + 4783030) * y + 263945)) * x + (((((((((((12313200) * y + 88598720) * y + 283515484) * y + 528751766) * y + 633528868) * y + 507379493) * y + 273986313) * y + 98151614) * y + 22254084) * y + 2877457) * y + 161137)) * x + (((((((((((5198232) * y + 38112204) * y + 123616692) * y + 232883592) * y + 281363224) * y + 227118526) * y + 123687252) * y + 44747052) * y + 10265132) * y + 1345686) * y + 76526)) * x + (((((((((((1717872) * y + 12690576) * y + 41391228) * y + 78341118) * y + 95094358) * y + 77186454) * y + 42331624) * y + 15453604) * y + 3585756) * y + 476624) * y + 27538)) * x + (((((((((((419352) * y + 3101476) * y + 10128944) * y + 19208312) * y + 23386980) * y + 19069978) * y + 10527176) * y + 3877176) * y + 909942) * y + 122654) * y + 7202)) * x + (((((((((((69624) * y + 514340) * y + 1679768) * y + 3189702) * y + 3894710) * y + 3190542) * y + 1773090) * y + 658936) * y + 156436) * y + 21384) * y + 1276)) * x + (((((((((((6840) * y + 50492) * y + 165000) * y + 313952) * y + 384706) * y + 316800) * y + 177306) * y + 66496) * y + 15966) * y + 2212) * y + 134)) * x + (((((((((((288) * y + 2128) * y + 6968) * y + 13300) * y + 16368) * y + 13554) * y + 7638) * y + 2888) * y + 700) * y + 98) * y + 6)

/- The definitions of `Q₃,Q₄,P₃,P₄` above are generated from the exact
recurrence.  `Q₃,Q₄` are the numerator polynomials in the paper, while
`P₃,P₄` are their Möbius transforms. -/

/-- Every displayed coefficient of `P₃` is nonnegative, and its constant
coefficient is positive. -/
theorem P₃_pos {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 < P₃ x y := by
  unfold P₃
  positivity

/-- Every displayed coefficient of `P₄` is nonnegative, and its constant
coefficient is positive. -/
theorem P₄_pos {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 < P₄ x y := by
  unfold P₄
  positivity

/- Kernel-checked Möbius identity for the cubic numerator. -/
set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
theorem Q₃_mobius (x y : ℝ) (hx : 1 + x ≠ 0) (hy : 1 + y ≠ 0) :
    (1 + x) ^ 15 * (1 + y) ^ 10 *
        Q₃ (x / (1 + x)) (y / (1 + y)) = P₃ x y := by
  unfold Q₃ P₃
  field_simp [hx, hy]
  ring

/- Kernel-checked Möbius identity for the quartic numerator. -/
set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
theorem Q₄_mobius (x y : ℝ) (hx : 1 + x ≠ 0) (hy : 1 + y ≠ 0) :
    (1 + x) ^ 16 * (1 + y) ^ 10 *
        Q₄ (x / (1 + x)) (y / (1 + y)) = P₄ x y := by
  unfold Q₄ P₄
  field_simp [hx, hy]
  ring

/-- Positivity of the cubic numerator on the parameter rectangle. -/
theorem Q₃_pos {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) : 0 < Q₃ p z := by
  let x := p / (1 - p)
  let y := z / (1 - z)
  have hpd : 0 < 1 - p := sub_pos.mpr hp₁
  have hzd : 0 < 1 - z := sub_pos.mpr hz₁
  have hx₀ : 0 ≤ x := by dsimp [x]; positivity
  have hy₀ : 0 ≤ y := by dsimp [y]; positivity
  have hx₁ : 0 < 1 + x := by positivity
  have hy₁ : 0 < 1 + y := by positivity
  have hxp : x / (1 + x) = p := by
    dsimp [x]
    field_simp [hpd.ne']
    ring
  have hyz : y / (1 + y) = z := by
    dsimp [y]
    field_simp [hzd.ne']
    ring
  have hm := Q₃_mobius x y hx₁.ne' hy₁.ne'
  rw [hxp, hyz] at hm
  have hfac : 0 < (1 + x) ^ 15 * (1 + y) ^ 10 := by positivity
  have hmul : 0 < (1 + x) ^ 15 * (1 + y) ^ 10 * Q₃ p z := by
    rw [hm]
    exact P₃_pos hx₀ hy₀
  rcases (mul_pos_iff.mp hmul) with h | h
  · exact h.2
  · exact (not_lt_of_ge hfac.le h.1).elim

/-- Positivity of the quartic numerator on the parameter rectangle. -/
theorem Q₄_pos {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 ≤ z) (hz₁ : z < 1) : 0 < Q₄ p z := by
  let x := p / (1 - p)
  let y := z / (1 - z)
  have hpd : 0 < 1 - p := sub_pos.mpr hp₁
  have hzd : 0 < 1 - z := sub_pos.mpr hz₁
  have hx₀ : 0 ≤ x := by dsimp [x]; positivity
  have hy₀ : 0 ≤ y := by dsimp [y]; positivity
  have hx₁ : 0 < 1 + x := by positivity
  have hy₁ : 0 < 1 + y := by positivity
  have hxp : x / (1 + x) = p := by
    dsimp [x]
    field_simp [hpd.ne']
    ring
  have hyz : y / (1 + y) = z := by
    dsimp [y]
    field_simp [hzd.ne']
    ring
  have hm := Q₄_mobius x y hx₁.ne' hy₁.ne'
  rw [hxp, hyz] at hm
  have hfac : 0 < (1 + x) ^ 16 * (1 + y) ^ 10 := by positivity
  have hmul : 0 < (1 + x) ^ 16 * (1 + y) ^ 10 * Q₄ p z := by
    rw [hm]
    exact P₄_pos hx₀ hy₀
  rcases (mul_pos_iff.mp hmul) with h | h
  · exact h.2
  · exact (not_lt_of_ge hfac.le h.1).elim

/-- If both Taylor-bracket certificates are negative, then the bracket
containing the exponential is negative as well. -/
theorem exp_bracket_neg {p z C D : ℝ} (hv : 0 < v p z)
    (h₃ : C + T₃ p z * D < 0) (h₄ : C + T₄ p z * D < 0) :
    C + Real.exp (-(v p z)) * D < 0 := by
  by_cases hD : 0 ≤ D
  · have hTaylor : Real.exp (-(v p z)) ≤ T₄ p z := by
      exact (exp_neg_lt_taylor₄ hv).le
    have hle := add_le_add_right (mul_le_mul_of_nonneg_right hTaylor hD) C
    have hle' : C + Real.exp (-(v p z)) * D ≤ C + T₄ p z * D := by
      simpa [add_comm] using hle
    exact hle'.trans_lt h₄
  · have hD' : D ≤ 0 := le_of_not_ge hD
    have hTaylor : T₃ p z ≤ Real.exp (-(v p z)) := by
      exact (taylor₃_lt_exp_neg hv).le
    have hle := add_le_add_right (mul_le_mul_of_nonpos_right hTaylor hD') C
    have hle' : C + Real.exp (-(v p z)) * D ≤ C + T₃ p z * D := by
      simpa [add_comm] using hle
    exact hle'.trans_lt h₃

/-- The third recurrence bracket is strictly negative throughout the open
parameter rectangle. -/
theorem C₃_exp_D₃_neg {p z : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p < 1)
    (hz₀ : 0 < z) (hz₁ : z < 1) :
    C₃ p z + Real.exp (-(v p z)) * D₃ p z < 0 := by
  have hq₃ : 0 < Q₃ p z := Q₃_pos hp₀ hp₁ hz₀.le hz₁
  have hq₄ : 0 < Q₄ p z := Q₄_pos hp₀ hp₁ hz₀.le hz₁
  have h₃ : C₃ p z + T₃ p z * D₃ p z < 0 := by
    rw [C₃_add_T₃_mul_D₃_eq_Q₃ hp₀ hp₁ hz₀.le hz₁]
    have hc : 0 < c p := by unfold c; positivity
    have hden : 0 < 24 * (1 - p) * (1 + p) ^ 7 * (1 - z) *
        (1 + z) ^ 5 * (1 + p * z) ^ 5 := by positivity
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hden
  have h₄ : C₃ p z + T₄ p z * D₃ p z < 0 := by
    rw [C₃_add_T₄_mul_D₃_eq_Q₄ hp₀ hp₁ hz₀.le hz₁]
    have hc : 0 < c p := by unfold c; positivity
    have hden : 0 < 48 * (1 - p) * (1 + p) ^ 7 *
        (1 + z) ^ 5 * (1 + p * z) ^ 5 := by positivity
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) hden
  apply exp_bracket_neg
  · unfold v
    positivity
  · exact h₃
  · exact h₄

end AsymLaplaceCertificate

open Set


/-!
# An endpoint maximum criterion

This is the short calculus argument used after proving that the derivative
of the asymmetric-Laplace objective is strictly concave.
-/

/-- If `f'` is strictly concave on `[0,1]` and `f'(1)=0`, then `f` cannot
strictly exceed both endpoint values at an interior point. -/
theorem le_max_endpoints_of_deriv_strictConcave
    {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hfd : DifferentiableOn ℝ f (Ioo (0 : ℝ) 1))
    (hconc : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (deriv f))
    (hone : deriv f 1 = 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ max (f 0) (f 1) := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  rcases hx0.eq_or_lt with rfl | hx0
  · exact le_max_left _ _
  rcases hx1.eq_or_lt with rfl | hx1
  · exact le_max_right _ _
  by_contra hnot
  have hmax : max (f 0) (f 1) < f x := lt_of_not_ge hnot
  have h0 : f 0 < f x := (le_max_left (f 0) (f 1)).trans_lt hmax
  have h1 : f 1 < f x := (le_max_right (f 0) (f 1)).trans_lt hmax

  have hcont0x : ContinuousOn f (Icc (0 : ℝ) x) :=
    hf.mono (Icc_subset_Icc_right hx1.le)
  have hdiff0x : DifferentiableOn ℝ f (Ioo (0 : ℝ) x) :=
    hfd.mono (Ioo_subset_Ioo_right hx1.le)
  obtain ⟨c, hc, hcderiv⟩ :=
    exists_deriv_eq_slope f hx0 hcont0x hdiff0x
  have hcpos : 0 < deriv f c := by
    rw [hcderiv]
    positivity

  have hcontx1 : ContinuousOn f (Icc x (1 : ℝ)) :=
    hf.mono (Icc_subset_Icc_left hx0.le)
  have hdiffx1 : DifferentiableOn ℝ f (Ioo x (1 : ℝ)) :=
    hfd.mono (Ioo_subset_Ioo_left hx0.le)
  obtain ⟨d, hd, hdderiv⟩ :=
    exists_deriv_eq_slope f hx1 hcontx1 hdiffx1
  have hdneg : deriv f d < 0 := by
    rw [hdderiv]
    have hden : 0 < (1 : ℝ) - x := sub_pos.mpr hx1
    exact div_neg_of_neg_of_pos (sub_neg.mpr h1) hden

  have hcIcc : c ∈ Icc (0 : ℝ) 1 := ⟨hc.1.le, hc.2.trans hx1 |>.le⟩
  have h1Icc : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hcd : c < d := hc.2.trans hd.1
  have hdseg : d ∈ openSegment ℝ c 1 := by
    rw [openSegment_eq_Ioo (hcd.trans hd.2)]
    exact ⟨hcd, hd.2⟩
  have hstrict := hconc.lt_on_openSegment hcIcc h1Icc
    (ne_of_lt (hcd.trans hd.2)) hdseg
  rw [hone, min_eq_right hcpos.le] at hstrict
  exact (not_lt_of_ge hstrict.le) hdneg

/-- A directly usable version: negativity of the third derivative on
`(0,1)` makes the first derivative strictly concave. -/
theorem le_max_endpoints_of_third_deriv_neg
    {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hfd : DifferentiableOn ℝ f (Ioo (0 : ℝ) 1))
    (hf' : ContinuousOn (deriv f) (Icc (0 : ℝ) 1))
    (hthird : ∀ x ∈ Ioo (0 : ℝ) 1, (deriv^[3]) f x < 0)
    (hone : deriv f 1 = 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ max (f 0) (f 1) := by
  apply le_max_endpoints_of_deriv_strictConcave hf hfd _ hone
  apply strictConcaveOn_of_deriv2_neg (convex_Icc (0 : ℝ) 1) hf'
  intro x hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
  simpa only [Function.iterate_succ_apply] using hthird x hx'

/-- A coordinate-free recurrence version of the same endpoint argument.
Here `w<0` is the derivative of a decreasing parameter `u`, while
`k₁,k₂,k₃` are the first three derivatives of `k₀` with respect
to `u`.  This form avoids constructing the inverse change of variables. -/
theorem le_max_endpoints_of_decreasing_recurrence
    {k₀ k₁ k₂ k₃ w : ℝ → ℝ}
    (hc₀ : ContinuousOn k₀ (Icc (0 : ℝ) 1))
    (hc₁ : ContinuousOn k₁ (Ico (0 : ℝ) 1))
    (hc₂ : ContinuousOn k₂ (Ioo (0 : ℝ) 1))
    (hd₀ : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt k₀ (w x * k₁ x) x)
    (hd₁ : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt k₁ (w x * k₂ x) x)
    (hd₂ : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt k₂ (w x * k₃ x) x)
    (hw : ∀ x ∈ Ioo (0 : ℝ) 1, w x < 0)
    (hk₃ : ∀ x ∈ Ioo (0 : ℝ) 1, k₃ x < 0)
    (hk₁zero : k₁ 0 = 0) :
    ∀ x ∈ Icc (0 : ℝ) 1, k₀ x ≤ max (k₀ 0) (k₀ 1) := by
  intro x hx
  rcases hx.1.eq_or_lt with rfl | hx0
  · exact le_max_left _ _
  rcases hx.2.eq_or_lt with rfl | hx1
  · exact le_max_right _ _
  by_contra hnot
  have hmax : max (k₀ 0) (k₀ 1) < k₀ x := lt_of_not_ge hnot
  have hleft : k₀ 0 < k₀ x := (le_max_left _ _).trans_lt hmax
  have hright : k₀ 1 < k₀ x := (le_max_right _ _).trans_lt hmax

  obtain ⟨c, hc, hcSlope⟩ := exists_hasDerivAt_eq_slope k₀
    (fun y ↦ w y * k₁ y) hx0
    (hc₀.mono (Icc_subset_Icc_right hx1.le))
    (fun y hy ↦ hd₀ y ⟨hy.1, hy.2.trans hx1⟩)
  have hk₁c : k₁ c < 0 := by
    have hslope : 0 < (k₀ x - k₀ 0) / (x - 0) := by positivity
    have hprod : 0 < w c * k₁ c := by simpa [hcSlope] using hslope
    rcases mul_pos_iff.mp hprod with h | h
    · exact (not_lt_of_ge (hw c ⟨hc.1, hc.2.trans hx1⟩).le h.1).elim
    · exact h.2

  obtain ⟨d, hd, hdSlope⟩ := exists_hasDerivAt_eq_slope k₀
    (fun y ↦ w y * k₁ y) hx1
    (hc₀.mono (Icc_subset_Icc_left hx0.le))
    (fun y hy ↦ hd₀ y ⟨hx0.trans hy.1, hy.2⟩)
  have hk₁d : 0 < k₁ d := by
    have hslope : (k₀ 1 - k₀ x) / (1 - x) < 0 := by
      exact div_neg_of_neg_of_pos (sub_neg.mpr hright) (sub_pos.mpr hx1)
    have hprod : w d * k₁ d < 0 := by simpa [hdSlope] using hslope
    rcases mul_neg_iff.mp hprod with h | h
    · exact (not_lt_of_ge (hw d ⟨hx0.trans hd.1, hd.2⟩).le h.1).elim
    · exact h.2

  obtain ⟨e, he, heSlope⟩ := exists_hasDerivAt_eq_slope k₁
    (fun y ↦ w y * k₂ y) hc.1
    (hc₁.mono (fun y hy ↦ ⟨hy.1, hy.2.trans_lt (hc.2.trans hx1)⟩))
    (fun y hy ↦ hd₁ y ⟨hy.1, hy.2.trans (hc.2.trans hx1)⟩)
  have hk₂e : 0 < k₂ e := by
    have hslope : (k₁ c - k₁ 0) / (c - 0) < 0 := by
      rw [hk₁zero]
      exact div_neg_of_neg_of_pos (by simpa using hk₁c) (by simpa using hc.1)
    have hprod : w e * k₂ e < 0 := by simpa [heSlope] using hslope
    rcases mul_neg_iff.mp hprod with h | h
    · exact (not_lt_of_ge (hw e ⟨he.1, he.2.trans (hc.2.trans hx1)⟩).le h.1).elim
    · exact h.2

  have hcd : c < d := hc.2.trans hd.1
  obtain ⟨f, hf, hfSlope⟩ := exists_hasDerivAt_eq_slope k₁
    (fun y ↦ w y * k₂ y) hcd
    (hc₁.mono (fun y hy ↦
      ⟨(hc.1.trans_le hy.1).le, hy.2.trans_lt hd.2⟩))
    (fun y hy ↦ hd₁ y ⟨hc.1.trans hy.1, hy.2.trans hd.2⟩)
  have hk₂f : k₂ f < 0 := by
    have hnum : 0 < k₁ d - k₁ c := by linarith
    have hslope : 0 < (k₁ d - k₁ c) / (d - c) :=
      div_pos hnum (sub_pos.mpr hcd)
    have hprod : 0 < w f * k₂ f := by simpa [hfSlope] using hslope
    rcases mul_pos_iff.mp hprod with h | h
    · exact (not_lt_of_ge (hw f ⟨hc.1.trans hf.1, hf.2.trans hd.2⟩).le h.1).elim
    · exact h.2

  have hef : e < f := he.2.trans hf.1
  obtain ⟨r, hr, hrSlope⟩ := exists_hasDerivAt_eq_slope k₂
    (fun y ↦ w y * k₃ y) hef
    (hc₂.mono (fun y hy ↦ ⟨he.1.trans_le hy.1,
      hy.2.trans_lt (hf.2.trans hd.2)⟩))
    (fun y hy ↦ hd₂ y ⟨he.1.trans hy.1,
      hy.2.trans (hf.2.trans hd.2)⟩)
  have hslope : (k₂ f - k₂ e) / (f - e) < 0 := by
    have hefval : k₂ f < k₂ e := by linarith
    exact div_neg_of_neg_of_pos (sub_neg.mpr hefval)
      (sub_pos.mpr hef)
  have hprodneg : w r * k₃ r < 0 := by simpa [hrSlope] using hslope
  have hprodpos : 0 < w r * k₃ r := mul_pos_of_neg_of_neg
    (hw r ⟨he.1.trans hr.1, hr.2.trans (hf.2.trans hd.2)⟩)
    (hk₃ r ⟨he.1.trans hr.1, hr.2.trans (hf.2.trans hd.2)⟩)
  exact (not_lt_of_ge hprodpos.le) hprodneg

open Filter Set


/-!
# Calculus for the asymmetric-Laplace parametrization

This file contains the analytic change-of-variables calculation used in
Claim (iii).  The polynomial sign certificates are kept separately in
`AsymLaplaceCertificate`.
-/

namespace AsymLaplaceCertificate

/-- The parameter `z = alpha / sqrt (1+p^2)`. -/
def z (alpha p : ℝ) : ℝ := alpha / Real.sqrt (c p)

lemma z_nonneg_lt_one {alpha p : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) :
    0 ≤ z alpha p ∧ z alpha p < 1 := by
  constructor
  · unfold z
    positivity
  · have hc1 : 1 ≤ c p := by
      unfold c
      nlinarith [sq_nonneg p]
    have hc0 : 0 ≤ c p := le_trans (by norm_num) hc1
    have hs : 1 ≤ Real.sqrt (c p) := by
      nlinarith [Real.sq_sqrt hc0, Real.sqrt_nonneg (c p)]
    have hspos : 0 < Real.sqrt (c p) := Real.sqrt_pos.2 (by
      unfold c
      positivity)
    unfold z
    have hdiv : alpha / Real.sqrt (c p) ≤ alpha := by
      rw [div_le_iff₀ hspos]
      nlinarith
    exact hdiv.trans_lt ha1

/-- The abbreviation `q=1-p`. -/
def q (p : ℝ) : ℝ := 1 - p

/-- The squared asymmetry parameter `u=(1-p)^2/(1+p^2)`. -/
def u (p : ℝ) : ℝ := q p ^ 2 / c p

lemma c_pos (p : ℝ) : 0 < c p := by
  dsimp [c]
  positivity

lemma hasDerivAt_c (p : ℝ) : HasDerivAt c (2 * p) p := by
  have h := (hasDerivAt_const p (1 : ℝ)).add ((hasDerivAt_id p).pow 2)
  change HasDerivAt (fun x : ℝ => 1 + x ^ 2)
    (0 + (2 : ℝ) * p ^ (2 - 1) * 1) p at h
  apply h.congr_deriv
  norm_num

lemma hasDerivAt_z (alpha p : ℝ) :
    HasDerivAt (z alpha) (-p * z alpha p / c p) p := by
  change HasDerivAt (fun t : ℝ => alpha / Real.sqrt (c t))
    (-p * (alpha / Real.sqrt (c p)) / c p) p
  have hc : c p ≠ 0 := ne_of_gt (c_pos p)
  have hs := (hasDerivAt_c p).sqrt hc
  have hs0 : Real.sqrt (c p) ≠ 0 := Real.sqrt_ne_zero'.mpr (c_pos p)
  have hz := (hasDerivAt_const p alpha).div hs hs0
  apply hz.congr_deriv
  rw [Real.sq_sqrt (c_pos p).le]
  field_simp [hs0, hc]
  ring

lemma hasDerivAt_q (p : ℝ) : HasDerivAt q (-1) p := by
  have h := (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
  change HasDerivAt (fun x : ℝ => 1 - x) (0 - 1) p at h
  exact h.congr_deriv (by norm_num)

lemma hasDerivAt_u (p : ℝ) :
    HasDerivAt u (-2 * (1 - p ^ 2) / c p ^ 2) p := by
  change HasDerivAt (fun t : ℝ => (1 - t) ^ 2 / c t)
    (-2 * (1 - p ^ 2) / c p ^ 2) p
  have hc : c p ≠ 0 := ne_of_gt (c_pos p)
  have hu := ((hasDerivAt_q p).pow 2).div (hasDerivAt_c p) hc
  apply hu.congr_deriv
  dsimp [q, c]
  field_simp
  ring

lemma M_mul_uDeriv {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    M p * (-2 * (1 - p ^ 2) / c p ^ 2) = 1 := by
  have hne : 1 - p ^ 2 ≠ 0 := by nlinarith
  have hc : c p ≠ 0 := ne_of_gt (c_pos p)
  dsimp [M]
  field_simp

abbrev Point := ℝ × ℝ

/-- The curve `(p,z(alpha,p))` in the two-dimensional parameter space. -/
def path (alpha p : ℝ) : Point := (p, z alpha p)

/-- Its tangent vector. -/
def tangent (p z0 : ℝ) : Point := (1, -p * z0 / c p)

lemma hasDerivAt_path (alpha p : ℝ) :
    HasDerivAt (path alpha) (tangent p (z alpha p)) p := by
  change HasDerivAt (fun t : ℝ => (t, z alpha t))
    ((1 : ℝ), -p * z alpha p / c p) p
  exact (hasDerivAt_id p).prodMk (hasDerivAt_z alpha p)

/-- Along the curve `p -> (p,z(alpha,p))`, the derivative of `F` is the
operator `L = partial_p - (pz/c) partial_z` from the certificate file. -/
lemma hasDerivAt_along_L
    {F : ℝ → ℝ → ℝ} {alpha p : ℝ}
    (hF : DifferentiableAt ℝ (Function.uncurry F) (path alpha p)) :
    HasDerivAt (fun t => F t (z alpha t)) (L F p (z alpha p)) p := by
  let DF := fderiv ℝ (Function.uncurry F) (path alpha p)
  have hfull : HasFDerivAt (Function.uncurry F) DF (path alpha p) :=
    hF.hasFDerivAt
  change HasFDerivAt (Function.uncurry F) DF (p, z alpha p) at hfull
  have hp : HasDerivAt (fun t : ℝ => F t (z alpha p)) (DF (1, 0)) p := by
    have hpathp : HasDerivAt (fun t : ℝ => (t, z alpha p))
        ((1 : ℝ), (0 : ℝ)) p :=
      (hasDerivAt_id p).prodMk (hasDerivAt_const p (z alpha p))
    have h := hfull.comp_hasDerivAt p hpathp
    change HasDerivAt (fun t : ℝ => F t (z alpha p)) (DF (1, 0)) p at h
    exact h
  have hzpart : HasDerivAt (fun w : ℝ => F p w) (DF (0, 1)) (z alpha p) := by
    have hpathz : HasDerivAt (fun w : ℝ => (p, w))
        ((0 : ℝ), (1 : ℝ)) (z alpha p) :=
      (hasDerivAt_const (z alpha p) p).prodMk (hasDerivAt_id (z alpha p))
    have h := hfull.comp_hasDerivAt (z alpha p) hpathz
    change HasDerivAt (fun w : ℝ => F p w) (DF (0, 1)) (z alpha p) at h
    exact h
  have halong := hfull.comp_hasDerivAt p (hasDerivAt_path alpha p)
  change HasDerivAt (fun t : ℝ => F t (z alpha t))
    (DF (tangent p (z alpha p))) p at halong
  apply halong.congr_deriv
  rw [show tangent p (z alpha p) =
      (1, 0) + (-p * z alpha p / c p) • (0, 1) by
        ext <;> simp [tangent]]
  rw [map_add, map_smul]
  rw [← hp.deriv, ← hzpart.deriv]
  simp only [smul_eq_mul]
  unfold L
  ring

/-- The exponential factor multiplying the `C`-part of the recurrence. -/
def EC (alpha p : ℝ) : ℝ := Real.exp (-(z alpha p * q p))

/-- The exponential factor multiplying the `D`-part of the recurrence. -/
def ED (p : ℝ) : ℝ := Real.exp (p - 1)

lemma hasDerivAt_EC (alpha p : ℝ) :
    HasDerivAt (EC alpha)
      (EC alpha p * (z alpha p * (1 + p) / c p)) p := by
  change HasDerivAt (fun t : ℝ => Real.exp (-(z alpha t * q t)))
    (Real.exp (-(z alpha p * q p)) *
      (z alpha p * (1 + p) / c p)) p
  have harg := ((hasDerivAt_z alpha p).mul (hasDerivAt_q p)).neg
  change HasDerivAt (fun t : ℝ => -(z alpha t * q t)) _ p at harg
  have hexp := harg.exp
  change HasDerivAt (fun t : ℝ => Real.exp (-(z alpha t * q t))) _ p at hexp
  apply hexp.congr_deriv
  have hc : c p ≠ 0 := ne_of_gt (c_pos p)
  dsimp [q, c]
  field_simp
  ring

lemma hasDerivAt_ED (p : ℝ) : HasDerivAt ED (ED p) p := by
  change HasDerivAt (fun t : ℝ => Real.exp (t - 1)) (Real.exp (p - 1)) p
  have h := ((hasDerivAt_id p).sub_const 1).exp
  change HasDerivAt (fun t : ℝ => Real.exp (t - 1))
    (Real.exp (p - 1) * 1) p at h
  apply h.congr_deriv
  simp

/-- The derivative `du/dp`. -/
def w (p : ℝ) : ℝ := -2 * (1 - p ^ 2) / c p ^ 2

lemma hasDerivAt_u' (p : ℝ) : HasDerivAt u (w p) p := by
  exact hasDerivAt_u p

lemma M_mul_w {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    M p * w p = 1 := by
  exact M_mul_uDeriv hp0 hp1

/-- A term of the form preserved by the `C,D` recurrence. -/
def Kterm (alpha : ℝ) (C D : ℝ → ℝ → ℝ) (p : ℝ) : ℝ :=
  EC alpha p * C p (z alpha p) + ED p * D p (z alpha p)

/-- One recurrence step is exactly differentiation with respect to `u`:
along the `p`-curve, the derivative of `Kterm C D` is `u'(p)` times
`Kterm (Cstep C) (Dstep D)`. -/
lemma hasDerivAt_Kterm_step
    {alpha p : ℝ} {C D : ℝ → ℝ → ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (hC : DifferentiableAt ℝ (Function.uncurry C) (path alpha p))
    (hD : DifferentiableAt ℝ (Function.uncurry D) (path alpha p)) :
    HasDerivAt (Kterm alpha C D)
      (w p * Kterm alpha (Cstep C) (Dstep D) p) p := by
  have hCalong := hasDerivAt_along_L hC
  have hDalong := hasDerivAt_along_L hD
  have hCterm := (hasDerivAt_EC alpha p).mul hCalong
  change HasDerivAt
    (fun t : ℝ => EC alpha t * C t (z alpha t))
    ((EC alpha p * (z alpha p * (1 + p) / c p)) *
      C p (z alpha p) + EC alpha p * L C p (z alpha p)) p at hCterm
  have hDterm := (hasDerivAt_ED p).mul hDalong
  change HasDerivAt
    (fun t : ℝ => ED t * D t (z alpha t))
    (ED p * D p (z alpha p) + ED p * L D p (z alpha p)) p at hDterm
  have hsum := hCterm.add hDterm
  change HasDerivAt (Kterm alpha C D) _ p at hsum
  apply hsum.congr_deriv
  have hMw : M p * w p = 1 := M_mul_w hp0 hp1
  unfold Kterm Cstep Dstep
  ring_nf at hMw ⊢
  rw [hMw]
  ring

/-- The four functions occurring after zero, one, two and three recurrence
steps. -/
def K₀ (alpha : ℝ) : ℝ → ℝ := Kterm alpha A B
def K₁ (alpha : ℝ) : ℝ → ℝ := Kterm alpha C₁ D₁
def K₂ (alpha : ℝ) : ℝ → ℝ := Kterm alpha C₂ D₂
def K₃ (alpha : ℝ) : ℝ → ℝ := Kterm alpha C₃ D₃

lemma hasDerivAt_K₀
    {alpha p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hA : DifferentiableAt ℝ (Function.uncurry A) (path alpha p))
    (hB : DifferentiableAt ℝ (Function.uncurry B) (path alpha p)) :
    HasDerivAt (K₀ alpha) (w p * K₁ alpha p) p := by
  obtain ⟨hz0, hz1⟩ := z_nonneg_lt_one ha0 ha1 (p := p)
  have h := hasDerivAt_Kterm_step hp0 hp1 hA hB
  change HasDerivAt (Kterm alpha A B) (w p * K₁ alpha p) p
  apply h.congr_deriv
  unfold K₁ Kterm
  rw [Cstep_A_eq_C₁ hp0.le hp1 hz0 hz1,
    Dstep_B_eq_D₁ hp0.le hp1 hz0 hz1]

lemma hasDerivAt_K₁
    {alpha p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hC₁ : DifferentiableAt ℝ (Function.uncurry C₁) (path alpha p))
    (hD₁ : DifferentiableAt ℝ (Function.uncurry D₁) (path alpha p)) :
    HasDerivAt (K₁ alpha) (w p * K₂ alpha p) p := by
  obtain ⟨hz0, hz1⟩ := z_nonneg_lt_one ha0 ha1 (p := p)
  have h := hasDerivAt_Kterm_step hp0 hp1 hC₁ hD₁
  change HasDerivAt (Kterm alpha C₁ D₁) (w p * K₂ alpha p) p
  apply h.congr_deriv
  unfold K₂ Kterm
  rw [Cstep_C₁_eq_C₂ hp0.le hp1 hz0 hz1,
    Dstep_D₁_eq_D₂ hp0.le hp1 hz0 hz1]

lemma hasDerivAt_K₂
    {alpha p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hC₂ : DifferentiableAt ℝ (Function.uncurry C₂) (path alpha p))
    (hD₂ : DifferentiableAt ℝ (Function.uncurry D₂) (path alpha p)) :
    HasDerivAt (K₂ alpha) (w p * K₃ alpha p) p := by
  obtain ⟨hz0, hz1⟩ := z_nonneg_lt_one ha0 ha1 (p := p)
  have h := hasDerivAt_Kterm_step hp0 hp1 hC₂ hD₂
  change HasDerivAt (Kterm alpha C₂ D₂) (w p * K₃ alpha p) p
  apply h.congr_deriv
  unfold K₃ Kterm
  rw [Cstep_C₂_eq_C₃ hp0.le hp1 hz0 hz1,
    Dstep_D₂_eq_D₃ hp0.le hp1 hz0 hz1]

/-- The two exponential factors combine into the Taylor argument `v`. -/
lemma ED_eq_EC_mul_exp_neg_v (alpha p : ℝ) :
    ED p = EC alpha p * Real.exp (-(v p (z alpha p))) := by
  unfold ED EC v q
  rw [← Real.exp_add]
  congr 1
  ring

/-- The third recurrence term is the exponential factor times precisely the
bracket controlled by the algebraic certificate. -/
lemma K₃_factor (alpha p : ℝ) :
    K₃ alpha p = EC alpha p *
      (C₃ p (z alpha p) + Real.exp (-(v p (z alpha p))) *
        D₃ p (z alpha p)) := by
  unfold K₃ Kterm
  rw [ED_eq_EC_mul_exp_neg_v]
  ring

lemma K₃_neg_of_bracket_neg {alpha p : ℝ}
    (hneg : C₃ p (z alpha p) + Real.exp (-(v p (z alpha p))) *
      D₃ p (z alpha p) < 0) :
    K₃ alpha p < 0 := by
  rw [K₃_factor]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hneg

/-- The endpoint argument, separated from the algebraic proof that `K₃<0`.
The final theorem supplies `hK₃` from the polynomial certificate and
`hK₁zero` by the endpoint computation. -/
theorem K₀_le_max_endpoints_of_K₃_neg
    {alpha : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hc₀ : ContinuousOn (K₀ alpha) (Icc (0 : ℝ) 1))
    (hc₁ : ContinuousOn (K₁ alpha) (Ico (0 : ℝ) 1))
    (hc₂ : ContinuousOn (K₂ alpha) (Ioo (0 : ℝ) 1))
    (hA : ∀ p ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (Function.uncurry A) (path alpha p))
    (hB : ∀ p ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (Function.uncurry B) (path alpha p))
    (hC₁ : ∀ p ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (Function.uncurry C₁) (path alpha p))
    (hD₁ : ∀ p ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (Function.uncurry D₁) (path alpha p))
    (hC₂ : ∀ p ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (Function.uncurry C₂) (path alpha p))
    (hD₂ : ∀ p ∈ Ioo (0 : ℝ) 1,
      DifferentiableAt ℝ (Function.uncurry D₂) (path alpha p))
    (hK₃ : ∀ p ∈ Ioo (0 : ℝ) 1, K₃ alpha p < 0)
    (hK₁zero : K₁ alpha 0 = 0) :
    ∀ p ∈ Icc (0 : ℝ) 1,
      K₀ alpha p ≤ max (K₀ alpha 0) (K₀ alpha 1) := by
  apply le_max_endpoints_of_decreasing_recurrence
    hc₀ hc₁ hc₂
  · intro p hp
    exact hasDerivAt_K₀ hp.1 hp.2 ha0 ha1 (hA p hp) (hB p hp)
  · intro p hp
    exact hasDerivAt_K₁ hp.1 hp.2 ha0 ha1 (hC₁ p hp) (hD₁ p hp)
  · intro p hp
    exact hasDerivAt_K₂ hp.1 hp.2 ha0 ha1 (hC₂ p hp) (hD₂ p hp)
  · intro p hp
    have hprod : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
    have hnum : 0 < 1 - p ^ 2 := by nlinarith
    have hden : 0 < c p ^ 2 := sq_pos_of_pos (c_pos p)
    unfold w
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hnum) hden
  · exact hK₃
  · exact hK₁zero

end AsymLaplaceCertificate

open Set Filter Real


/-!
# Regularity of the asymmetric-Laplace recurrence

Continuity and differentiability facts needed by the endpoint argument.
-/

namespace AsymLaplaceCertificate

lemma continuousAt_K₀ {alpha p : ℝ} (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hp0 : 0 ≤ p) :
    ContinuousAt (K₀ alpha) p := by
  have hz0 : 0 ≤ z alpha p := by
    unfold z
    positivity
  have hz1 : z alpha p < 1 := by
    have hs : 1 ≤ Real.sqrt (c p) := by
      have hc1 : 1 ≤ c p := by
        unfold c
        nlinarith [sq_nonneg p]
      have hc0 : 0 ≤ c p := le_trans (by norm_num) hc1
      nlinarith [Real.sq_sqrt hc0, Real.sqrt_nonneg (c p)]
    unfold z
    have hspos : 0 < Real.sqrt (c p) := by
      exact Real.sqrt_pos.2 (c_pos p)
    have hdiv : alpha / Real.sqrt (c p) ≤ alpha := by
      rw [div_le_iff₀ hspos]
      nlinarith
    exact hdiv.trans_lt ha1
  have hzcont : ContinuousAt (z alpha) p :=
    (hasDerivAt_z alpha p).continuousAt
  have hzminus : 1 - z alpha p ≠ 0 := by linarith
  have hzsq : 1 - z alpha p ^ 2 ≠ 0 := by nlinarith
  have hpp : 1 + p ≠ 0 := by positivity
  have hpz : 1 + z alpha p * p ≠ 0 := by positivity
  unfold K₀ Kterm EC ED A B q
  fun_prop (disch := positivity)

lemma continuousOn_K₀ {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) :
    ContinuousOn (K₀ alpha) (Icc (0 : ℝ) 1) := by
  intro p hp
  exact (show ContinuousAt (K₀ alpha) p from
    by exact continuousAt_K₀ ha0 ha1 hp.1).continuousWithinAt

lemma continuousAt_K₁ {alpha p : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hp0 : 0 ≤ p) (hp1 : p < 1) : ContinuousAt (K₁ alpha) p := by
  obtain ⟨hz0, hz1⟩ := z_nonneg_lt_one ha0 ha1 (p := p)
  have hzcont : ContinuousAt (z alpha) p := (hasDerivAt_z alpha p).continuousAt
  have hpm : p - 1 ≠ 0 := by linarith
  have hpp : p + 1 ≠ 0 := by positivity
  have hzm : z alpha p - 1 ≠ 0 := by linarith
  have hzp : z alpha p + 1 ≠ 0 := by positivity
  have hpz : p * z alpha p + 1 ≠ 0 := by positivity
  unfold K₁ Kterm EC ED C₁ D₁ C1r D1r C1num D1num C1den D1den q
  fun_prop (disch := positivity)

lemma continuousOn_K₁ {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) :
    ContinuousOn (K₁ alpha) (Ico (0 : ℝ) 1) := by
  intro p hp
  exact (continuousAt_K₁ ha0 ha1 hp.1 hp.2).continuousWithinAt

lemma continuousAt_K₂ {alpha p : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hp0 : 0 < p) (hp1 : p < 1) : ContinuousAt (K₂ alpha) p := by
  obtain ⟨hz0, hz1⟩ := z_nonneg_lt_one ha0 ha1 (p := p)
  have hzcont : ContinuousAt (z alpha) p := (hasDerivAt_z alpha p).continuousAt
  have hpm : p - 1 ≠ 0 := by linarith
  have hpp : p + 1 ≠ 0 := by positivity
  have hzm : z alpha p - 1 ≠ 0 := by linarith
  have hzp : z alpha p + 1 ≠ 0 := by positivity
  have hpz : p * z alpha p + 1 ≠ 0 := by positivity
  unfold K₂ Kterm EC ED C₂ D₂ C2r D2r C2num D2num C2den D2den q
  fun_prop (disch := positivity)

lemma continuousOn_K₂ {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) :
    ContinuousOn (K₂ alpha) (Ioo (0 : ℝ) 1) := by
  intro p hp
  exact (continuousAt_K₂ ha0 ha1 hp.1 hp.2).continuousWithinAt

lemma differentiableAt_A {alpha p : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hp0 : 0 < p) :
    DifferentiableAt ℝ (Function.uncurry A) (path alpha p) := by
  obtain ⟨hz0, hz1⟩ := z_nonneg_lt_one ha0 ha1 (p := p)
  have hzm : 1 - z alpha p ≠ 0 := by linarith
  have hpz : 1 + z alpha p * p ≠ 0 := by positivity
  unfold path A
  fun_prop (disch := positivity)

lemma differentiableAt_B {alpha p : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hp0 : 0 < p) :
    DifferentiableAt ℝ (Function.uncurry B) (path alpha p) := by
  obtain ⟨hz0, hz1⟩ := z_nonneg_lt_one ha0 ha1 (p := p)
  have hpp : 1 + p ≠ 0 := by positivity
  have hzsq : 1 - z alpha p ^ 2 ≠ 0 := by nlinarith
  unfold path B
  fun_prop (disch := positivity)

lemma differentiableAt_C₁ {alpha p : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    DifferentiableAt ℝ (Function.uncurry C₁) (path alpha p) := by
  obtain ⟨hz0, hz1⟩ := z_nonneg_lt_one ha0 ha1 (p := p)
  have hpm : p - 1 ≠ 0 := by linarith
  have hzm : z alpha p - 1 ≠ 0 := by linarith
  have hpz : p * z alpha p + 1 ≠ 0 := by positivity
  unfold path C₁ C1r C1num C1den
  fun_prop (disch := positivity)

lemma differentiableAt_D₁ {alpha p : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    DifferentiableAt ℝ (Function.uncurry D₁) (path alpha p) := by
  obtain ⟨hz0, hz1⟩ := z_nonneg_lt_one ha0 ha1 (p := p)
  have hpm : p - 1 ≠ 0 := by linarith
  have hpp : p + 1 ≠ 0 := by positivity
  have hzm : z alpha p - 1 ≠ 0 := by linarith
  have hzp : z alpha p + 1 ≠ 0 := by positivity
  unfold path D₁ D1r D1num D1den
  fun_prop (disch := positivity)

lemma differentiableAt_C₂ {alpha p : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    DifferentiableAt ℝ (Function.uncurry C₂) (path alpha p) := by
  obtain ⟨hz0, hz1⟩ := z_nonneg_lt_one ha0 ha1 (p := p)
  have hpm : p - 1 ≠ 0 := by linarith
  have hzm : z alpha p - 1 ≠ 0 := by linarith
  have hpz : p * z alpha p + 1 ≠ 0 := by positivity
  unfold path C₂ C2r C2num C2den
  fun_prop (disch := positivity)

lemma differentiableAt_D₂ {alpha p : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    DifferentiableAt ℝ (Function.uncurry D₂) (path alpha p) := by
  obtain ⟨hz0, hz1⟩ := z_nonneg_lt_one ha0 ha1 (p := p)
  have hpm : p - 1 ≠ 0 := by linarith
  have hpp : p + 1 ≠ 0 := by positivity
  have hzm : z alpha p - 1 ≠ 0 := by linarith
  have hzp : z alpha p + 1 ≠ 0 := by positivity
  unfold path D₂ D2r D2num D2den
  fun_prop (disch := positivity)

lemma K₁_zero (alpha : ℝ) : K₁ alpha 0 = 0 := by
  simp [K₁, Kterm, C₁, D₁, C1r, D1r, C1num, D1num]

end AsymLaplaceCertificate

open MeasureTheory Set Filter Real
open scoped Topology


/-!
# The endpoint `alpha = 1`

The estimates in the interior calculation are first proved for
`0 < alpha < 1`.  This file supplies the dominated-convergence argument
needed to pass to `alpha = 1`.
-/

/-- Dominated convergence on one exponential ray. -/
theorem tendsto_rayIntegral_at_one
    {alpha : ℕ → ℝ} (halpha : ∀ n, 0 ≤ alpha n)
    (halpha_one : Tendsto alpha atTop (𝓝 1)) (d scale : ℝ) :
    Tendsto
      (fun n ↦ ∫ t in Ioi (0 : ℝ),
        gAlpha (alpha n) |d + scale * t| * Real.exp (-t))
      atTop
      (𝓝 (∫ t in Ioi (0 : ℝ),
        gAlpha 1 |d + scale * t| * Real.exp (-t))) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (fun t : ℝ ↦ Real.exp (-t))
  · intro n
    have hcont : Continuous
        (fun t : ℝ ↦
          gAlpha (alpha n) |d + scale * t| * Real.exp (-t)) := by
      unfold gAlpha
      fun_prop
    exact hcont.aestronglyMeasurable
  · exact integrableOn_exp_neg_Ioi 0
  · intro n
    filter_upwards with t
    have hg0 : 0 ≤ gAlpha (alpha n) |d + scale * t| :=
      gAlpha_nonneg (halpha n) (abs_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hg0 (Real.exp_pos _).le)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le
      (gAlpha_le_one (halpha n) (abs_nonneg _))
  · filter_upwards with t
    have hcont : Continuous
        (fun beta : ℝ ↦
          gAlpha beta |d + scale * t| * Real.exp (-t)) := by
      unfold gAlpha
      fun_prop
    exact hcont.continuousAt.tendsto.comp halpha_one

/-- Sequential continuity of the asymmetric-Laplace objective at
`alpha = 1`, from any nonnegative sequence. -/
theorem tendsto_asymLaplaceObjective_at_one
    {alpha : ℕ → ℝ} (halpha : ∀ n, 0 ≤ alpha n)
    (halpha_one : Tendsto alpha atTop (𝓝 1))
    (a b : ℝ) :
    Tendsto (fun n ↦ asymLaplaceObjective (alpha n) a b) atTop
      (𝓝 (asymLaplaceObjective 1 a b)) := by
  let d := a - b
  have hleft := tendsto_rayIntegral_at_one halpha halpha_one d (-a)
  have hright := tendsto_rayIntegral_at_one halpha halpha_one d b
  have hsum := (hleft.const_mul (a / (a + b))).add
    (hright.const_mul (b / (a + b)))
  simpa only [asymLaplaceObjective, d, sub_eq_add_neg, neg_mul] using hsum

/-- The symmetric endpoint expression is continuous at `alpha=1`. -/
theorem continuousAt_laplaceValue_one : ContinuousAt laplaceValue 1 := by
  unfold laplaceValue
  fun_prop (disch := positivity)

/-- Sequential continuity of the shifted endpoint at `alpha=1`.  This
proof uses its integral representation, thereby avoiding the removable
singularity in its closed formula. -/
theorem tendsto_shiftedValue_at_one
    {alpha : ℕ → ℝ} (halpha : ∀ n, 0 ≤ alpha n)
    (halpha_one : Tendsto alpha atTop (𝓝 1)) :
    Tendsto (fun n ↦ shiftedValue (alpha n)) atTop
      (𝓝 (shiftedValue 1)) := by
  have hobj := tendsto_asymLaplaceObjective_at_one
    halpha halpha_one 1 0
  have hfun : (fun n ↦ shiftedValue (alpha n)) =
      (fun n ↦ asymLaplaceObjective (alpha n) 1 0) := by
    funext n
    exact (asymLaplaceObjective_shifted (alpha n) (halpha n)).symm
  rw [hfun]
  simpa only [asymLaplaceObjective_shifted 1 (by norm_num)] using hobj

/-- Sequential continuity of the symmetric endpoint value at `alpha=1`. -/
theorem tendsto_laplaceValue_at_one
    {alpha : ℕ → ℝ} (halpha_one : Tendsto alpha atTop (𝓝 1)) :
    Tendsto (fun n ↦ laplaceValue (alpha n)) atTop
      (𝓝 (laplaceValue 1)) :=
  continuousAt_laplaceValue_one.tendsto.comp halpha_one

/-- Passing an asymmetric-Laplace bound from `0<alpha<1` to the remaining
endpoint `alpha=1`.  The proof approaches `1` through
`beta_n = 1 - 1/(n+1)` and uses the preceding dominated-convergence
theorem; no closed formula with a removable singularity is used. -/
theorem asymLaplaceObjective_one_le_max_of_lt_one
    (a b : ℝ)
    (hbound : ∀ beta : ℝ, 0 < beta → beta < 1 →
      asymLaplaceObjective beta a b ≤
        max (shiftedValue beta) (laplaceValue beta)) :
    asymLaplaceObjective 1 a b ≤
      max (shiftedValue 1) (laplaceValue 1) := by
  let beta : ℕ → ℝ := fun n ↦ 1 - 1 / ((n : ℝ) + 1)
  have hbeta_nonneg : ∀ n, 0 ≤ beta n := by
    intro n
    have hden : 0 < (n : ℝ) + 1 := by positivity
    rw [show beta n = (n : ℝ) / ((n : ℝ) + 1) by
      dsimp [beta]
      field_simp
      ring]
    positivity
  have hbeta_one : Tendsto beta atTop (𝓝 1) := by
    have hzero :
        Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [beta] using (tendsto_const_nhds.sub hzero :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) - 1 / ((n : ℝ) + 1))
        atTop (𝓝 (1 - 0)))
  have hleft := tendsto_asymLaplaceObjective_at_one
    hbeta_nonneg hbeta_one a b
  have hright :=
    (tendsto_shiftedValue_at_one hbeta_nonneg hbeta_one).max
      (tendsto_laplaceValue_at_one hbeta_one)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  apply hbound (beta n)
  · rw [show beta n = (n : ℝ) / ((n : ℝ) + 1) by
      dsimp [beta]
      field_simp
      ring]
    positivity
  · dsimp [beta]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hone : 1 / ((n : ℝ) + 1) > 0 := by positivity
    linarith


open Set


/-!
# Normalization of asymmetric-Laplace parameters

This file contains only the elementary normalization of nonnegative
parameters `a,b` satisfying `a^2+b^2=1`.  The analytic estimate for the
interior parameter is deliberately kept in a separate theorem.
-/

namespace AsymLaplaceClaim

/-- The scale corresponding to the ratio `p=b/a`. -/
def regularScale (p : ℝ) : ℝ := 1 / Real.sqrt (1 + p ^ 2)

lemma one_add_sq_pos (p : ℝ) : 0 < 1 + p ^ 2 := by positivity

lemma regularScale_pos (p : ℝ) : 0 < regularScale p := by
  unfold regularScale
  positivity

lemma regularScale_sq (p : ℝ) :
    regularScale p ^ 2 = 1 / (1 + p ^ 2) := by
  unfold regularScale
  rw [div_pow, one_pow, Real.sq_sqrt (one_add_sq_pos p).le]

lemma eq_regularScale_of_nonneg_of_sq
    {a p : ℝ} (ha : 0 ≤ a)
    (ha_sq : a ^ 2 = 1 / (1 + p ^ 2)) :
    a = regularScale p := by
  have hsquares : a ^ 2 = regularScale p ^ 2 := by
    rw [regularScale_sq]
    exact ha_sq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with h | h
  · exact h
  · have hspos := regularScale_pos p
    nlinarith

/-- Interior normalization: if `0<b<a`, then `p=b/a` belongs to `(0,1)`
and `(a,b)=(1,p)/sqrt(1+p^2)`. -/
theorem ordered_interior_normalization
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hba : b < a)
    (hab : a ^ 2 + b ^ 2 = 1) :
    let p := b / a
    p ∈ Ioo (0 : ℝ) 1 ∧
      a = regularScale p ∧ b = p * regularScale p := by
  let p := b / a
  have ha_pos : 0 < a := hb.trans hba
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hp_pos : 0 < p := div_pos hb ha_pos
  have hp_lt : p < 1 := (div_lt_one ha_pos).mpr hba
  have hbpa : b = p * a := by
    dsimp [p]
    field_simp
  have hnorm : (1 + p ^ 2) * a ^ 2 = 1 := by
    calc
      (1 + p ^ 2) * a ^ 2 = a ^ 2 + (p * a) ^ 2 := by ring
      _ = a ^ 2 + b ^ 2 := by rw [hbpa]
      _ = 1 := hab
  have hden : 1 + p ^ 2 ≠ 0 := ne_of_gt (one_add_sq_pos p)
  have ha_sq : a ^ 2 = 1 / (1 + p ^ 2) := by
    apply (eq_div_iff hden).2
    calc
      a ^ 2 * (1 + p ^ 2) = (1 + p ^ 2) * a ^ 2 := by ring
      _ = 1 := hnorm
  have ha_scale : a = regularScale p :=
    eq_regularScale_of_nonneg_of_sq ha ha_sq
  refine ⟨⟨hp_pos, hp_lt⟩, ha_scale, ?_⟩
  calc
    b = p * a := hbpa
    _ = p * regularScale p := by rw [ha_scale]

/-- The three ordered cases: the one-sided endpoint, the symmetric endpoint,
or the regular interior family. -/
def OrderedNormalForm (a b : ℝ) : Prop :=
  (b = 0 ∧ a = 1) ∨
  (a = b ∧ a = regularScale 1 ∧ b = regularScale 1) ∨
  ∃ p ∈ Ioo (0 : ℝ) 1,
    a = regularScale p ∧ b = p * regularScale p

theorem ordered_normal_form
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ^ 2 + b ^ 2 = 1) (horder : b ≤ a) :
    OrderedNormalForm a b := by
  rcases hb.eq_or_lt with rfl | hb_pos
  · left
    constructor
    · rfl
    · nlinarith
  rcases horder.eq_or_lt with hba | hba
  · right
    left
    have ha_sq : a ^ 2 = 1 / (1 + (1 : ℝ) ^ 2) := by
      rw [hba] at hab
      norm_num
      nlinarith
    have ha_scale : a = regularScale 1 :=
      eq_regularScale_of_nonneg_of_sq ha ha_sq
    exact ⟨hba.symm, ha_scale, by simpa [hba] using ha_scale⟩
  · right
    right
    obtain ⟨hp, ha_scale, hb_scale⟩ :=
      ordered_interior_normalization ha hb_pos hba hab
    exact ⟨b / a, hp, ha_scale, hb_scale⟩

/-- After possibly swapping `a` and `b`, every normalized nonnegative pair
is in the ordered normal form. -/
theorem normal_form_up_to_swap
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ^ 2 + b ^ 2 = 1) :
    (b ≤ a ∧ OrderedNormalForm a b) ∨
      (a ≤ b ∧ OrderedNormalForm b a) := by
  rcases le_total b a with hba | hab_order
  · exact Or.inl ⟨hba, ordered_normal_form ha hb hab hba⟩
  · have hswap : b ^ 2 + a ^ 2 = 1 := by nlinarith
    exact Or.inr ⟨hab_order,
      ordered_normal_form hb ha hswap hab_order⟩

/-- A generic symmetry reduction: to prove a swap-invariant assertion for
all normalized nonnegative pairs, it is enough to prove it when `b ≤ a`. -/
theorem of_ordered_of_swap_symmetric
    {P : ℝ → ℝ → Prop}
    (hsymm : ∀ x y, P x y ↔ P y x)
    (hordered : ∀ {x y : ℝ}, 0 ≤ x → 0 ≤ y →
      x ^ 2 + y ^ 2 = 1 → y ≤ x → P x y)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ^ 2 + b ^ 2 = 1) : P a b := by
  rcases le_total b a with hba | hab_order
  · exact hordered ha hb hab hba
  · apply (hsymm a b).mpr
    apply hordered hb ha
    · nlinarith
    · exact hab_order

end AsymLaplaceClaim

open MeasureTheory Set Filter Real


/-!
# Assembly lemmas for the asymmetric-Laplace calculation

This file identifies the genuine integral formula with the rational--
exponential function used by the calculus certificate, and records its two
endpoint values.  Throughout this file `0 ≤ alpha < 1`; the remaining value
`alpha=1` is supplied by `AsymLaplaceLimit`.
-/

namespace AsymLaplaceAssembly

open AsymLaplaceCertificate

lemma regularScale_le_one (p : ℝ) : regularScale p ≤ 1 := by
  have harg : (1 : ℝ) ≤ 1 + p ^ 2 := by nlinarith [sq_nonneg p]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (1 + p ^ 2) := by
    simpa using Real.sqrt_le_sqrt harg
  have hsqrt_pos : 0 < Real.sqrt (1 + p ^ 2) := by positivity
  unfold regularScale
  exact (div_le_one hsqrt_pos).2 hsqrt

lemma certificate_z_eq (alpha p : ℝ) :
    z alpha p = alpha * regularScale p := by
  unfold z c regularScale
  simp [div_eq_mul_inv]

/-- The regular integral formula is exactly `K₀`, the initial term of the
calculus recurrence. -/
theorem kHatRegular_eq_K₀
    (alpha p : ℝ) (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    kHatRegular alpha p = K₀ alpha p := by
  have hscale := regularScale_le_one p
  have hzlt : alpha * regularScale p < 1 := by
    have hmul : alpha * regularScale p ≤ alpha := by
      nlinarith [mul_nonneg halpha (sub_nonneg.mpr hscale)]
    exact hmul.trans_lt halpha1
  rw [kHatRegular_eq_exp_regular alpha p halpha hp hp1 hzlt.ne]
  unfold K₀ Kterm EC ED q
  rw [certificate_z_eq]
  rfl

lemma regularScale_zero : regularScale 0 = 1 := by
  simp [regularScale]

lemma regularScale_one : regularScale 1 = Real.sqrt 2 / 2 := by
  have hspos : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsquare : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  unfold regularScale
  norm_num
  field_simp [hspos.ne']
  nlinarith

/-- The `p=0` endpoint is the shifted exponential. -/
theorem K₀_zero_eq_shiftedValue
    (alpha : ℝ) (halpha : 0 ≤ alpha) (halpha1 : alpha < 1) :
    K₀ alpha 0 = shiftedValue alpha := by
  calc
    K₀ alpha 0 = kHatRegular alpha 0 :=
      (kHatRegular_eq_K₀ alpha 0 halpha halpha1 (by norm_num)
        (by norm_num)).symm
    _ = asymLaplaceObjective alpha (regularScale 0)
          (0 * regularScale 0) :=
      (asymLaplaceObjective_regular alpha 0 halpha (by norm_num)
        (by norm_num)).symm
    _ = asymLaplaceObjective alpha 1 0 := by
      rw [regularScale_zero]
      norm_num
    _ = shiftedValue alpha := asymLaplaceObjective_shifted alpha halpha

/-- The `p=1` endpoint is the symmetric isotropic Laplace law. -/
theorem K₀_one_eq_laplaceValue
    (alpha : ℝ) (halpha : 0 ≤ alpha) (halpha1 : alpha < 1) :
    K₀ alpha 1 = laplaceValue alpha := by
  calc
    K₀ alpha 1 = kHatRegular alpha 1 :=
      (kHatRegular_eq_K₀ alpha 1 halpha halpha1 (by norm_num)
        (by norm_num)).symm
    _ = asymLaplaceObjective alpha (regularScale 1)
          (1 * regularScale 1) :=
      (asymLaplaceObjective_regular alpha 1 halpha (by norm_num)
        (by norm_num)).symm
    _ = asymLaplaceObjective alpha (Real.sqrt 2 / 2)
          (Real.sqrt 2 / 2) := by
      rw [regularScale_one]
      ring_nf
    _ = laplaceValue alpha := asymLaplaceObjective_symmetric alpha halpha

/-- Direct rewrite of the genuine expectation at a regular parameter as
the function controlled by the calculus certificate. -/
theorem asymLaplaceObjective_regular_eq_K₀
    (alpha p : ℝ) (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    asymLaplaceObjective alpha (regularScale p) (p * regularScale p) =
      K₀ alpha p := by
  rw [asymLaplaceObjective_regular alpha p halpha hp hp1]
  exact kHatRegular_eq_K₀ alpha p halpha halpha1 hp hp1

/-! ## Regularity data for the recurrence theorem -/

-- The continuity, differentiability, and endpoint facts used below are
-- proved in `AsymLaplaceRegularity`.

lemma hasDerivAt_K₀_regular {alpha p : ℝ}
    (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (K₀ alpha) (w p * K₁ alpha p) p := by
  exact hasDerivAt_K₀ hp0 hp1 halpha halpha1
    (differentiableAt_A halpha halpha1 hp0)
    (differentiableAt_B halpha halpha1 hp0)

lemma hasDerivAt_K₁_regular {alpha p : ℝ}
    (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (K₁ alpha) (w p * K₂ alpha p) p := by
  exact hasDerivAt_K₁ hp0 hp1 halpha halpha1
    (differentiableAt_C₁ halpha halpha1 hp0 hp1)
    (differentiableAt_D₁ halpha halpha1 hp0 hp1)

lemma hasDerivAt_K₂_regular {alpha p : ℝ}
    (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (K₂ alpha) (w p * K₃ alpha p) p := by
  exact hasDerivAt_K₂ hp0 hp1 halpha halpha1
    (differentiableAt_C₂ halpha halpha1 hp0 hp1)
    (differentiableAt_D₂ halpha halpha1 hp0 hp1)

/-! ## Endpoint maximum, conditional only on the final sign certificate -/

/-- Once `K₃<0` on the open parameter interval has been supplied by the
polynomial certificate, the recurrence argument bounds `K₀` by its two
endpoint values. -/
theorem K₀_le_max_endpoint_values_of_K₃_neg
    {alpha : ℝ} (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hK₃ : ∀ p ∈ Ioo (0 : ℝ) 1, K₃ alpha p < 0) :
    ∀ p ∈ Icc (0 : ℝ) 1,
      K₀ alpha p ≤ max (shiftedValue alpha) (laplaceValue alpha) := by
  intro p hp
  have h := le_max_endpoints_of_decreasing_recurrence
    (continuousOn_K₀ halpha halpha1)
    (continuousOn_K₁ halpha halpha1)
    (continuousOn_K₂ halpha halpha1)
    (fun x hx ↦ hasDerivAt_K₀_regular halpha halpha1 hx.1 hx.2)
    (fun x hx ↦ hasDerivAt_K₁_regular halpha halpha1 hx.1 hx.2)
    (fun x hx ↦ hasDerivAt_K₂_regular halpha halpha1 hx.1 hx.2)
    (fun x hx ↦ by
      have hminus : 0 < 1 - x := sub_pos.mpr hx.2
      have hplus : 0 < 1 + x := by linarith [hx.1]
      have hnum : 0 < 1 - x ^ 2 := by
        nlinarith [mul_pos hminus hplus]
      have hden : 0 < c x ^ 2 := sq_pos_of_pos (c_pos x)
      unfold w
      exact div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by norm_num) hnum) hden)
    hK₃ (K₁_zero alpha) p hp
  simpa [K₀_zero_eq_shiftedValue alpha halpha halpha1,
    K₀_one_eq_laplaceValue alpha halpha halpha1] using h

/-- The corresponding bound for the genuine expectation at every regular
asymmetric-Laplace parameter. -/
theorem asymLaplaceObjective_regular_le_max_of_K₃_neg
    {alpha p : ℝ} (halpha : 0 ≤ alpha) (halpha1 : alpha < 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hK₃ : ∀ x ∈ Ioo (0 : ℝ) 1, K₃ alpha x < 0) :
    asymLaplaceObjective alpha (regularScale p) (p * regularScale p) ≤
      max (shiftedValue alpha) (laplaceValue alpha) := by
  rw [asymLaplaceObjective_regular_eq_K₀ alpha p halpha halpha1 hp hp1]
  exact K₀_le_max_endpoint_values_of_K₃_neg halpha halpha1 hK₃ p ⟨hp, hp1⟩

/-! ## The completed asymmetric-Laplace maximum -/

/-- The polynomial certificate supplies the final sign hypothesis required
by the recurrence argument. -/
theorem K₃_neg
    {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    ∀ p ∈ Ioo (0 : ℝ) 1, K₃ alpha p < 0 := by
  intro p hp
  obtain ⟨hz0, hz1⟩ :=
    z_nonneg_lt_one halpha.le halpha1 (p := p)
  have hzpos : 0 < z alpha p := by
    unfold z
    exact div_pos halpha (Real.sqrt_pos.2 (c_pos p))
  apply K₃_neg_of_bracket_neg
  exact C₃_exp_D₃_neg hp.1.le hp.2 hzpos hz1

/-- Claim (iii) for the regular parametrization and `0<alpha<1`. -/
theorem asymLaplaceObjective_regular_le_max
    {alpha p : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    asymLaplaceObjective alpha (regularScale p) (p * regularScale p) ≤
      max (shiftedValue alpha) (laplaceValue alpha) :=
  asymLaplaceObjective_regular_le_max_of_K₃_neg
    halpha.le halpha1 hp hp1 (K₃_neg halpha halpha1)

lemma claim_regularScale_eq (p : ℝ) :
    AsymLaplaceClaim.regularScale p = regularScale p := rfl

/-- Claim (iii) for arbitrary normalized nonnegative scales and
`0<alpha<1`. -/
theorem asymLaplaceObjective_le_max_of_lt_one
    {alpha a b : ℝ} (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1) :
    asymLaplaceObjective alpha a b ≤
      max (shiftedValue alpha) (laplaceValue alpha) := by
  apply AsymLaplaceClaim.of_ordered_of_swap_symmetric
    (P := fun x y ↦ asymLaplaceObjective alpha x y ≤
      max (shiftedValue alpha) (laplaceValue alpha))
  · intro x y
    rw [asymLaplaceObjective_swap alpha x y]
  · intro x y hx hy hxy hyx
    rcases AsymLaplaceClaim.ordered_normal_form hx hy hxy hyx with
      hshift | hrest
    · rcases hshift with ⟨rfl, rfl⟩
      rw [asymLaplaceObjective_shifted alpha halpha.le]
      exact le_max_left _ _
    · rcases hrest with hsym | hinterior
      · rcases hsym with ⟨hxy', hxscale, hyscale⟩
        rw [hxscale, hyscale, claim_regularScale_eq]
        simpa using asymLaplaceObjective_regular_le_max
          halpha halpha1 (p := (1 : ℝ)) (by norm_num) (by norm_num)
      · rcases hinterior with ⟨p, hp, hxscale, hyscale⟩
        rw [hxscale, hyscale, claim_regularScale_eq]
        exact asymLaplaceObjective_regular_le_max
          halpha halpha1 hp.1.le hp.2.le
  · exact ha
  · exact hb
  · exact hab

/-- Claim (iii) at `alpha=1`, obtained from the genuine integral formula by
dominated convergence. -/
theorem asymLaplaceObjective_le_max_at_one
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ^ 2 + b ^ 2 = 1) :
    asymLaplaceObjective 1 a b ≤
      max (shiftedValue 1) (laplaceValue 1) := by
  apply asymLaplaceObjective_one_le_max_of_lt_one a b
  intro beta hbeta hbeta1
  exact asymLaplaceObjective_le_max_of_lt_one
    hbeta hbeta1 ha hb hab

/-- Claim (iii), in the full range `0<alpha≤1`. -/
theorem asymLaplaceObjective_le_max
    {alpha a b : ℝ} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 = 1) :
    asymLaplaceObjective alpha a b ≤
      max (shiftedValue alpha) (laplaceValue alpha) := by
  rcases halpha1.lt_or_eq with halpha1' | rfl
  · exact asymLaplaceObjective_le_max_of_lt_one
      halpha halpha1' ha hb hab
  · exact asymLaplaceObjective_le_max_at_one ha hb hab

/-- The set of values of the asymmetric-Laplace objective over normalized
nonnegative ray scales. -/
def normalizedAsymLaplaceValues (alpha : ℝ) : Set ℝ :=
  {y | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a ^ 2 + b ^ 2 = 1 ∧
    y = asymLaplaceObjective alpha a b}

/-- The exact maximum statement for the normalized asymmetric-Laplace
family in Claim (iii): the bound is both universal and attained by one of
its two endpoint laws.  This theorem does not formalize the external
reduction from all two-piece densities (6) to this family. -/
theorem normalizedAsymLaplace_isGreatest
    {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) :
    IsGreatest (normalizedAsymLaplaceValues alpha)
      (max (shiftedValue alpha) (laplaceValue alpha)) := by
  constructor
  · rcases le_total (shiftedValue alpha) (laplaceValue alpha) with hSL | hLS
    · rw [max_eq_right hSL]
      let s : ℝ := Real.sqrt 2 / 2
      have hs : 0 ≤ s := by dsimp [s]; positivity
      have hnorm : s ^ 2 + s ^ 2 = 1 := by
        dsimp [s]
        have hsquare : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
          Real.sq_sqrt (by norm_num)
        nlinarith
      exact ⟨s, s, hs, hs, hnorm,
        (asymLaplaceObjective_symmetric alpha halpha.le).symm⟩
    · rw [max_eq_left hLS]
      exact ⟨1, 0, by norm_num, by norm_num, by norm_num,
        (asymLaplaceObjective_shifted alpha halpha.le).symm⟩
  · intro y hy
    rcases hy with ⟨a, b, ha, hb, hab, rfl⟩
    exact asymLaplaceObjective_le_max halpha halpha1 ha hb hab

end AsymLaplaceAssembly

end FlattenedExistenceSection17


/-!
Flattened source section: EndpointWitnesses.lean
-/

section FlattenedExistenceSection18

open Real Set MeasureTheory

namespace EndpointWitnesses

/-- The test function in the extremal problem. -/
def gAlpha (alpha x : ℝ) : ℝ :=
  (1 + alpha * |x|) * Real.exp (-alpha * |x|)

/-- The symmetric-Laplace endpoint value. -/
def S (alpha : ℝ) : ℝ :=
  2 * (1 + Real.sqrt 2 * alpha) / (Real.sqrt 2 + alpha) ^ 2

/-- The centered one-sided-exponential endpoint value.  This integral form is
continuous at `alpha = 1` and avoids an artificial removable singularity. -/
def L (alpha : ℝ) : ℝ :=
  Real.exp (-1) *
    ((∫ t in (0 : ℝ)..1, (1 + alpha * t) * Real.exp ((1 - alpha) * t)) +
      (1 + 2 * alpha) / (1 + alpha) ^ 2)

/-- Density of the isotropic symmetric Laplace law. -/
def laplaceDensity (x : ℝ) : ℝ :=
  (1 / Real.sqrt 2) * Real.exp (-(Real.sqrt 2 * |x|))

/-- Density of `E - 1`, where `E` is standard exponential. -/
def shiftedExpDensity (x : ℝ) : ℝ :=
  Set.indicator (Set.Ici (-1)) (fun y : ℝ ↦ Real.exp (-(y + 1))) x

/-- The density form in (6), with a real support set in place of extended-real
endpoints. -/
def twoPieceDensity
    (c beta delta m : ℝ) (support : Set ℝ) (x : ℝ) : ℝ :=
  Set.indicator support
    (fun y : ℝ ↦ Real.exp (c + beta * y - delta * max (y - m) 0)) x

theorem shiftedExpDensity_twoPiece (x : ℝ) :
    shiftedExpDensity x =
      twoPieceDensity (-1) (-1) 0 0 (Ici (-1 : ℝ)) x := by
  unfold shiftedExpDensity twoPieceDensity
  by_cases hx : x ∈ Ici (-1 : ℝ)
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    congr 1
    ring
  · simp [hx]

theorem laplaceDensity_twoPiece (x : ℝ) :
    laplaceDensity x =
      twoPieceDensity (Real.log (1 / Real.sqrt 2)) (Real.sqrt 2)
        (2 * Real.sqrt 2) 0 Set.univ x := by
  unfold laplaceDensity twoPieceDensity
  rw [Set.indicator_univ]
  have hinv : 0 < 1 / Real.sqrt (2 : ℝ) := by positivity
  by_cases hx : x ≤ 0
  · rw [abs_of_nonpos hx, max_eq_right (sub_nonpos.mpr hx)]
    rw [show Real.exp
        (Real.log (1 / Real.sqrt 2) + Real.sqrt 2 * x -
          2 * Real.sqrt 2 * 0) =
        Real.exp (Real.log (1 / Real.sqrt 2)) *
          Real.exp (Real.sqrt 2 * x) by
      rw [← Real.exp_add]
      congr 1
      ring]
    rw [Real.exp_log hinv]
    congr 1
    ring_nf
  · have hx0 : 0 ≤ x := (lt_of_not_ge hx).le
    rw [abs_of_nonneg hx0, max_eq_left (sub_nonneg.mpr hx0)]
    rw [show Real.exp
        (Real.log (1 / Real.sqrt 2) + Real.sqrt 2 * x -
          2 * Real.sqrt 2 * (x - 0)) =
        Real.exp (Real.log (1 / Real.sqrt 2)) *
          Real.exp (-(Real.sqrt 2 * x)) by
      rw [← Real.exp_add]
      congr 1
      ring]
    rw [Real.exp_log hinv]

/-- Every polynomial times a genuinely decaying exponential is integrable on
a right half-line. -/
lemma integrableOn_pow_mul_exp_mul_Ioi
    (n : ℕ) {k : ℝ} (hk : k < 0) (a : ℝ) :
    IntegrableOn (fun x : ℝ ↦ x ^ n * Real.exp (k * x)) (Ioi a) := by
  let t : ℝ := -k / 2
  have ht : t ≠ 0 := by
    dsimp [t]
    linarith
  have hplus : k + t < 0 := by
    dsimp [t]
    linarith
  have hminus : k - t < 0 := by
    dsimp [t]
    linarith
  have hiPlus : Integrable
      (fun x : ℝ ↦ Real.exp ((k + t) * x)) (volume.restrict (Ioi a)) :=
    integrableOn_exp_mul_Ioi hplus a
  have hiMinus : Integrable
      (fun x : ℝ ↦ Real.exp ((k - t) * x)) (volume.restrict (Ioi a)) :=
    integrableOn_exp_mul_Ioi hminus a
  exact ProbabilityTheory.integrable_pow_mul_exp_of_integrable_exp_mul
    (X := fun x : ℝ ↦ x) (v := k) (t := t) ht hiPlus hiMinus n

lemma tendsto_pow_mul_exp_neg_mul_atTop (n : ℕ) {r : ℝ} (hr : 0 < r) :
    Filter.Tendsto (fun x : ℝ ↦ x ^ n * Real.exp (-(r * x)))
      Filter.atTop (nhds 0) := by
  have hscale : Filter.Tendsto (fun x : ℝ ↦ r * x) Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos hr).2 Filter.tendsto_id
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp hscale
  have h' := (tendsto_const_nhds.mul h :
    Filter.Tendsto
      (fun x : ℝ ↦ (r ^ n)⁻¹ * ((r * x) ^ n * Real.exp (-(r * x))))
      Filter.atTop (nhds ((r ^ n)⁻¹ * 0)))
  convert h' using 1
  · funext x
    rw [mul_pow]
    field_simp [hr.ne']
  · simp

lemma integral_exp_neg_mul_Ioi_zero {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, Real.exp (-(r * x))) = 1 / r := by
  have h := integral_exp_mul_Ioi (a := -r) (by linarith) 0
  simpa [neg_mul, hr.ne'] using h

lemma integral_mul_exp_neg_mul_Ioi_zero {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, x * Real.exp (-(r * x))) = 1 / r ^ 2 := by
  let F : ℝ → ℝ := fun x ↦
    -(((r * x + 1) / r ^ 2) * Real.exp (-(r * x)))
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt F (x * Real.exp (-(r * x))) x := by
    intro x _hx
    dsimp [F]
    have hp : HasDerivAt (fun y : ℝ ↦ (r * y + 1) / r ^ 2)
        (r / r ^ 2) x := by
      simpa only [id_eq, mul_one, add_comm] using
        (((hasDerivAt_id x).const_mul r).const_add 1).div_const (r ^ 2)
    have he : HasDerivAt (fun y : ℝ ↦ Real.exp (-(r * y)))
        (Real.exp (-(r * x)) * (-r)) x := by
      simpa only [id_eq, mul_one, Pi.neg_apply] using
        (((hasDerivAt_id x).const_mul r).neg.exp)
    refine (hp.mul he).neg.congr_deriv ?_
    field_simp [hr.ne']
    ring
  have hint : IntegrableOn (fun x : ℝ ↦ x * Real.exp (-(r * x))) (Ioi 0) := by
    simpa only [pow_one, neg_mul] using
      (integrableOn_pow_mul_exp_mul_Ioi 1 (k := -r) (by linarith) 0)
  have hlim : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have h0 := tendsto_pow_mul_exp_neg_mul_atTop 0 hr
    have h1 := tendsto_pow_mul_exp_neg_mul_atTop 1 hr
    have hcomb := (h1.const_mul (r / r ^ 2)).add (h0.const_mul (1 / r ^ 2))
    have hneg := hcomb.neg
    convert hneg using 1
    · funext x
      dsimp [F]
      field_simp [hr.ne'] <;> ring
    · simp
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv hint hlim
  calc
    (∫ x : ℝ in Ioi 0, x * Real.exp (-(r * x))) = 0 - F 0 := h
    _ = 1 / r ^ 2 := by
      dsimp [F]
      field_simp [hr.ne']
      norm_num

lemma integral_sq_mul_exp_neg_mul_Ioi_zero {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-(r * x))) = 2 / r ^ 3 := by
  let F : ℝ → ℝ := fun x ↦
    -(((r ^ 2 * x ^ 2 + 2 * r * x + 2) / r ^ 3) *
      Real.exp (-(r * x)))
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt F (x ^ 2 * Real.exp (-(r * x))) x := by
    intro x _hx
    dsimp [F]
    have hp : HasDerivAt
        (fun y : ℝ ↦ (r ^ 2 * y ^ 2 + 2 * r * y + 2) / r ^ 3)
        ((2 * r ^ 2 * x + 2 * r) / r ^ 3) x := by
      have hp0 := (((((hasDerivAt_id x).pow 2).const_mul (r ^ 2)).add
        ((hasDerivAt_id x).const_mul (2 * r))).const_add 2).div_const (r ^ 3)
      have hp1 : HasDerivAt
          (fun y : ℝ ↦ (r ^ 2 * y ^ 2 + 2 * r * y + 2) / r ^ 3)
          ((r ^ 2 * ((2 : ℝ) * id x ^ (2 - 1) * 1) + 2 * r * 1) / r ^ 3) x := by
        apply hp0.congr_of_eventuallyEq
        filter_upwards [] with y
        simp only [id_eq, Pi.add_apply, Pi.pow_apply]
        ring
      refine hp1.congr_deriv ?_
      simp only [id_eq]
      ring
    have he : HasDerivAt (fun y : ℝ ↦ Real.exp (-(r * y)))
        (Real.exp (-(r * x)) * (-r)) x := by
      simpa only [id_eq, mul_one, Pi.neg_apply] using
        (((hasDerivAt_id x).const_mul r).neg.exp)
    refine (hp.mul he).neg.congr_deriv ?_
    field_simp [hr.ne']
    ring
  have hint : IntegrableOn (fun x : ℝ ↦ x ^ 2 * Real.exp (-(r * x))) (Ioi 0) := by
    simpa only [neg_mul] using
      (integrableOn_pow_mul_exp_mul_Ioi 2 (k := -r) (by linarith) 0)
  have hlim : Filter.Tendsto F Filter.atTop (nhds 0) := by
    have h0 := tendsto_pow_mul_exp_neg_mul_atTop 0 hr
    have h1 := tendsto_pow_mul_exp_neg_mul_atTop 1 hr
    have h2 := tendsto_pow_mul_exp_neg_mul_atTop 2 hr
    have hcomb := ((h2.const_mul (r ^ 2 / r ^ 3)).add
      (h1.const_mul (2 * r / r ^ 3))).add
      (h0.const_mul (2 / r ^ 3))
    have hneg := hcomb.neg
    convert hneg using 1
    · funext x
      dsimp [F]
      field_simp [hr.ne'] <;> ring
    · simp
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv hint hlim
  calc
    (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-(r * x))) = 0 - F 0 := h
    _ = 2 / r ^ 3 := by
      dsimp [F]
      field_simp [hr.ne']
      norm_num

lemma sqrt_two_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)

lemma sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)

theorem laplace_mass :
    (∫ x : ℝ, laplaceDensity x) = 1 := by
  change (∫ x : ℝ, (fun t : ℝ ↦
    (1 / Real.sqrt 2) * Real.exp (-(Real.sqrt 2 * t))) |x|) = 1
  rw [integral_comp_abs (f := fun t : ℝ ↦
      (1 / Real.sqrt 2) * Real.exp (-(Real.sqrt 2 * t))),
    MeasureTheory.integral_const_mul,
    integral_exp_neg_mul_Ioi_zero sqrt_two_pos]
  field_simp [sqrt_two_pos.ne']
  nlinarith [sqrt_two_sq]

theorem laplace_mean :
    (∫ x : ℝ, x * laplaceDensity x) = 0 := by
  have h := MeasureTheory.integral_neg_eq_self
    (fun x : ℝ ↦ x * laplaceDensity x) volume
  have hodd : (fun x : ℝ ↦ (-x) * laplaceDensity (-x)) =
      fun x : ℝ ↦ -(x * laplaceDensity x) := by
    funext x
    simp only [laplaceDensity, abs_neg]
    ring
  rw [hodd, MeasureTheory.integral_neg] at h
  linarith

theorem laplace_second_moment :
    (∫ x : ℝ, x ^ 2 * laplaceDensity x) = 1 := by
  rw [show (fun x : ℝ ↦ x ^ 2 * laplaceDensity x) =
      fun x : ℝ ↦ (fun t : ℝ ↦
        t ^ 2 * ((1 / Real.sqrt 2) * Real.exp (-(Real.sqrt 2 * t)))) |x| by
    funext x
    simp only [laplaceDensity]
    rw [sq_abs]]
  rw [integral_comp_abs (f := fun t : ℝ ↦
    t ^ 2 * ((1 / Real.sqrt 2) * Real.exp (-(Real.sqrt 2 * t))))]
  have hfun : (fun t : ℝ ↦
      t ^ 2 * ((1 / Real.sqrt 2) * Real.exp (-(Real.sqrt 2 * t)))) =
      fun t : ℝ ↦ (1 / Real.sqrt 2) *
        (t ^ 2 * Real.exp (-(Real.sqrt 2 * t))) := by
    funext t
    ring
  rw [hfun, MeasureTheory.integral_const_mul,
    integral_sq_mul_exp_neg_mul_Ioi_zero sqrt_two_pos]
  field_simp [sqrt_two_pos.ne']
  nlinarith [sqrt_two_sq]

theorem laplace_objective {alpha : ℝ} (halpha : 0 < alpha) :
    (∫ x : ℝ, gAlpha alpha x * laplaceDensity x) = S alpha := by
  let q := Real.sqrt 2 + alpha
  have hq : 0 < q := by
    dsimp [q]
    linarith [sqrt_two_pos]
  change (∫ x : ℝ, (fun t : ℝ ↦
    ((1 + alpha * t) * Real.exp (-alpha * t)) *
      ((1 / Real.sqrt 2) * Real.exp (-(Real.sqrt 2 * t)))) |x|) = S alpha
  rw [integral_comp_abs (f := fun t : ℝ ↦
    ((1 + alpha * t) * Real.exp (-alpha * t)) *
      ((1 / Real.sqrt 2) * Real.exp (-(Real.sqrt 2 * t))))]
  have hfun : (fun t : ℝ ↦
      ((1 + alpha * t) * Real.exp (-alpha * t)) *
        ((1 / Real.sqrt 2) * Real.exp (-(Real.sqrt 2 * t)))) =
      fun t : ℝ ↦ (1 / Real.sqrt 2) *
        (Real.exp (-(q * t)) + alpha *
          (t * Real.exp (-(q * t)))) := by
    funext t
    have hexp : Real.exp (-alpha * t) *
        Real.exp (-(Real.sqrt 2 * t)) = Real.exp (-(q * t)) := by
      rw [← Real.exp_add]
      dsimp [q]
      congr 1
      ring
    rw [show
      ((1 + alpha * t) * Real.exp (-alpha * t)) *
          ((1 / Real.sqrt 2) * Real.exp (-(Real.sqrt 2 * t))) =
        (1 / Real.sqrt 2) * (1 + alpha * t) *
          (Real.exp (-alpha * t) * Real.exp (-(Real.sqrt 2 * t))) by ring,
      hexp]
    ring
  rw [hfun, MeasureTheory.integral_const_mul]
  have h0 : IntegrableOn (fun t : ℝ ↦ Real.exp (-(q * t))) (Ioi 0) := by
    simpa only [pow_zero, one_mul, neg_mul] using
      (integrableOn_pow_mul_exp_mul_Ioi 0 (k := -q) (by linarith) 0)
  have h1 : IntegrableOn (fun t : ℝ ↦ t * Real.exp (-(q * t))) (Ioi 0) := by
    simpa only [pow_one, neg_mul] using
      (integrableOn_pow_mul_exp_mul_Ioi 1 (k := -q) (by linarith) 0)
  rw [MeasureTheory.integral_add h0 (h1.const_mul alpha),
    MeasureTheory.integral_const_mul,
    integral_exp_neg_mul_Ioi_zero hq,
    integral_mul_exp_neg_mul_Ioi_zero hq]
  dsimp [S, q]
  field_simp [sqrt_two_pos.ne', hq.ne']
  nlinarith [sqrt_two_sq]

/-- Translation of expectations under the density of `E - 1` to the
standard exponential half-line. -/
lemma shiftedExp_integral (h : ℝ → ℝ) :
    (∫ x : ℝ, h x * shiftedExpDensity x) =
      ∫ t : ℝ in Ioi 0, h (t - 1) * Real.exp (-t) := by
  let H : ℝ → ℝ := fun x ↦
    Set.indicator (Ici (-1))
      (fun y : ℝ ↦ h y * Real.exp (-(y + 1))) x
  have hpoint : (fun x : ℝ ↦ h x * shiftedExpDensity x) = H := by
    funext x
    by_cases hx : x ∈ Ici (-1)
    · simp [shiftedExpDensity, H, hx]
    · simp [shiftedExpDensity, H, hx]
  rw [hpoint]
  have hshift := MeasureTheory.integral_sub_right_eq_self (μ := volume) H 1
  rw [← hshift]
  have htranslated : (fun t : ℝ ↦ H (t - 1)) =
      Set.indicator (Ici 0)
        (fun t : ℝ ↦ h (t - 1) * Real.exp (-t)) := by
    funext t
    by_cases ht : 0 ≤ t
    · have hm : t - 1 ∈ Ici (-1) := by
        simp only [mem_Ici]
        linarith
      simp only [H, Set.indicator_of_mem hm,
        Set.indicator_of_mem (show t ∈ Ici 0 from ht)]
      congr 2
      ring
    · have hm : t - 1 ∉ Ici (-1) := by
        simp only [mem_Ici]
        linarith
      have ht' : t ∉ Ici 0 := ht
      simp only [H, Set.indicator_of_notMem hm,
        Set.indicator_of_notMem ht']
  rw [htranslated, MeasureTheory.integral_indicator measurableSet_Ici,
    integral_Ici_eq_integral_Ioi]

theorem shiftedExp_mass :
    (∫ x : ℝ, shiftedExpDensity x) = 1 := by
  have h := shiftedExp_integral (fun _ : ℝ ↦ 1)
  simpa only [one_mul, integral_exp_neg_Ioi_zero] using h

theorem shiftedExp_mean :
    (∫ x : ℝ, x * shiftedExpDensity x) = 0 := by
  rw [shiftedExp_integral]
  have h0 : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0
  have h1 : IntegrableOn (fun t : ℝ ↦ t * Real.exp (-t)) (Ioi 0) := by
    simpa only [pow_one, one_mul, neg_mul] using
      (integrableOn_pow_mul_exp_mul_Ioi 1 (k := -1) (by norm_num) 0)
  have hm0 : (∫ t : ℝ in Ioi 0, Real.exp (-t)) = 1 := by
    simpa only [one_mul, div_one] using
      integral_exp_neg_mul_Ioi_zero (by norm_num : (0 : ℝ) < 1)
  have hm1 : (∫ t : ℝ in Ioi 0, t * Real.exp (-t)) = 1 := by
    simpa only [one_mul, one_pow, div_one] using
      integral_mul_exp_neg_mul_Ioi_zero (by norm_num : (0 : ℝ) < 1)
  rw [show (fun t : ℝ ↦ (t - 1) * Real.exp (-t)) =
      fun t : ℝ ↦ t * Real.exp (-t) - Real.exp (-t) by
    funext t
    ring,
    MeasureTheory.integral_sub h1 h0,
    hm1, hm0]
  norm_num

theorem shiftedExp_second_moment :
    (∫ x : ℝ, x ^ 2 * shiftedExpDensity x) = 1 := by
  rw [shiftedExp_integral]
  have h0 : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Ioi 0) := by
    simpa only [neg_one_mul] using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0
  have h1 : IntegrableOn (fun t : ℝ ↦ t * Real.exp (-t)) (Ioi 0) := by
    simpa only [pow_one, one_mul, neg_mul] using
      (integrableOn_pow_mul_exp_mul_Ioi 1 (k := -1) (by norm_num) 0)
  have h2 : IntegrableOn (fun t : ℝ ↦ t ^ 2 * Real.exp (-t)) (Ioi 0) := by
    simpa only [one_mul, neg_mul] using
      (integrableOn_pow_mul_exp_mul_Ioi 2 (k := -1) (by norm_num) 0)
  have hfun : (fun t : ℝ ↦ (t - 1) ^ 2 * Real.exp (-t)) =
      fun t : ℝ ↦ (t ^ 2 * Real.exp (-t) -
        2 * (t * Real.exp (-t))) + Real.exp (-t) := by
    funext t
    ring
  rw [hfun]
  change (∫ t : ℝ in Ioi 0,
    (((fun u : ℝ ↦ u ^ 2 * Real.exp (-u)) -
      (fun u : ℝ ↦ 2 * (u * Real.exp (-u)))) +
      (fun u : ℝ ↦ Real.exp (-u))) t) = 1
  have hadd :
      (∫ t : ℝ in Ioi 0,
        (t ^ 2 * Real.exp (-t) - 2 * (t * Real.exp (-t))) + Real.exp (-t)) =
      (∫ t : ℝ in Ioi 0,
        t ^ 2 * Real.exp (-t) - 2 * (t * Real.exp (-t))) +
      ∫ t : ℝ in Ioi 0, Real.exp (-t) :=
    MeasureTheory.integral_add (h2.sub (h1.const_mul 2)) h0
  have hsub :
      (∫ t : ℝ in Ioi 0,
        t ^ 2 * Real.exp (-t) - 2 * (t * Real.exp (-t))) =
      (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-t)) -
      ∫ t : ℝ in Ioi 0, 2 * (t * Real.exp (-t)) :=
    MeasureTheory.integral_sub h2 (h1.const_mul 2)
  change (∫ t : ℝ in Ioi 0,
    (t ^ 2 * Real.exp (-t) - 2 * (t * Real.exp (-t))) + Real.exp (-t)) = 1
  rw [hadd, hsub, MeasureTheory.integral_const_mul]
  have hm0 : (∫ t : ℝ in Ioi 0, Real.exp (-t)) = 1 := by
    simpa only [one_mul, div_one] using
      integral_exp_neg_mul_Ioi_zero (by norm_num : (0 : ℝ) < 1)
  have hm1 : (∫ t : ℝ in Ioi 0, t * Real.exp (-t)) = 1 := by
    simpa only [one_mul, one_pow, div_one] using
      integral_mul_exp_neg_mul_Ioi_zero (by norm_num : (0 : ℝ) < 1)
  have hm2 : (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-t)) = 2 := by
    simpa only [one_mul, one_pow, div_one] using
      integral_sq_mul_exp_neg_mul_Ioi_zero (by norm_num : (0 : ℝ) < 1)
  rw [hm0, hm1, hm2]
  norm_num

end EndpointWitnesses

end FlattenedExistenceSection18


/-!
Flattened source section: EndpointWitnessBridge.lean
-/

section FlattenedExistenceSection19

open MeasureTheory Set


namespace EndpointWitnessBridge

theorem laplace_objective_eq_laplaceValue
    {alpha : ℝ} (halpha : 0 < alpha) :
    (∫ x : ℝ,
      EndpointWitnesses.gAlpha alpha x * EndpointWitnesses.laplaceDensity x) =
      laplaceValue alpha := by
  exact EndpointWitnesses.laplace_objective halpha

theorem shiftedExp_objective_eq_asymLaplaceObjective (alpha : ℝ) :
    (∫ x : ℝ,
      EndpointWitnesses.gAlpha alpha x * EndpointWitnesses.shiftedExpDensity x) =
      asymLaplaceObjective alpha 1 0 := by
  rw [EndpointWitnesses.shiftedExp_integral]
  have hobj : asymLaplaceObjective alpha 1 0 =
      (∫ t : ℝ in Ioi 0,
        gAlpha alpha |1 - t| * Real.exp (-t)) := by
    simp [asymLaplaceObjective]
  rw [hobj]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  unfold EndpointWitnesses.gAlpha gAlpha
  change (1 + alpha * |t - 1|) * Real.exp (-alpha * |t - 1|) *
      Real.exp (-t) =
    (1 + alpha * |1 - t|) * Real.exp (-alpha * |1 - t|) *
      Real.exp (-t)
  rw [abs_sub_comm t 1]

theorem shiftedExp_objective_eq_shiftedValue
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    (∫ x : ℝ,
      EndpointWitnesses.gAlpha alpha x * EndpointWitnesses.shiftedExpDensity x) =
      shiftedValue alpha := by
  rw [shiftedExp_objective_eq_asymLaplaceObjective]
  exact asymLaplaceObjective_shifted alpha halpha

end EndpointWitnessBridge

end FlattenedExistenceSection19


/-!
Flattened source section: TerminalBridge.lean
-/

section FlattenedExistenceSection20

open Real Set MeasureTheory
open scoped Interval

namespace LogConcaveFamily6

open LogConcaveClaimI

/-! ## Affine changes of variables on exponential rays -/

/-- Translation of a right-ray integral.  Endpoint choices are immaterial
for Lebesgue measure. -/
lemma integral_comp_add_Ioi (f : ℝ → ℝ) (A : ℝ) :
    (∫ t : ℝ in Ioi 0, f (A + t)) = ∫ x : ℝ in Ioi A, f x := by
  let H : ℝ → ℝ := Set.indicator (Ioi A) f
  calc
    (∫ t : ℝ in Ioi 0, f (A + t)) = ∫ t : ℝ, H (t + A) := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with t
      by_cases ht : t ∈ Ioi (0 : ℝ)
      · have htA : t + A ∈ Ioi A := by
          simpa [mem_Ioi] using add_lt_add_right ht A
        rw [Set.indicator_of_mem ht]
        change f (A + t) = H (t + A)
        have hH : H (t + A) = f (t + A) := by simp [H, htA]
        rw [hH]
        exact congrArg f (add_comm A t)
      · have htA : t + A ∉ Ioi A := by
          simp only [mem_Ioi, not_lt] at ht ⊢
          linarith
        rw [Set.indicator_of_notMem ht]
        change 0 = H (t + A)
        simp [H, htA]
    _ = ∫ x : ℝ, H x :=
      MeasureTheory.integral_add_right_eq_self H A
    _ = ∫ x : ℝ in Ioi A, f x := by
      exact MeasureTheory.integral_indicator measurableSet_Ioi

/-- Positive affine substitution `x = A + t / lambda` on a right ray. -/
lemma integral_Ioi_affine (f : ℝ → ℝ) (A lambda : ℝ)
    (hlambda : 0 < lambda) :
    (∫ x : ℝ in Ioi A, f x) =
      lambda⁻¹ * ∫ t : ℝ in Ioi 0, f (A + t / lambda) := by
  have hinv : 0 < lambda⁻¹ := inv_pos.mpr hlambda
  have hs := MeasureTheory.integral_comp_mul_left_Ioi
    (fun y : ℝ ↦ f (A + y)) 0 hinv
  have htranslate := integral_comp_add_Ioi f A
  simp only [mul_zero, inv_inv, smul_eq_mul] at hs
  rw [← htranslate]
  calc
    (∫ x : ℝ in Ioi 0, f (A + x)) =
        lambda⁻¹ * (lambda * ∫ x : ℝ in Ioi 0, f (A + x)) := by
          field_simp [hlambda.ne']
    _ = lambda⁻¹ * ∫ t : ℝ in Ioi 0, f (A + t / lambda) := by
      congr 1
      rw [← hs]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      congr 1
      simp [div_eq_mul_inv, mul_comm]

/-- Reflection turns a left ray into a right ray. -/
lemma integral_Iic_eq_Ioi_reflect (f : ℝ → ℝ) (m : ℝ) :
    (∫ x : ℝ in Iic m, f x) = ∫ y : ℝ in Ioi (-m), f (-y) := by
  simpa only [neg_neg] using
    (integral_comp_neg_Iic m (fun y : ℝ ↦ f (-y)))

/-- Positive affine substitution `x = m - t / lambda` on a left ray. -/
lemma integral_Iic_affine (f : ℝ → ℝ) (m lambda : ℝ)
    (hlambda : 0 < lambda) :
    (∫ x : ℝ in Iic m, f x) =
      lambda⁻¹ * ∫ t : ℝ in Ioi 0, f (m - t / lambda) := by
  rw [integral_Iic_eq_Ioi_reflect]
  rw [integral_Ioi_affine (fun y : ℝ ↦ f (-y)) (-m) lambda hlambda]
  apply congrArg (fun z : ℝ ↦ lambda⁻¹ * z)
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  congr 1
  ring_nf

/-! ## A one-piece exponential on a half-line -/

/-- When the kink height is zero, the artificial split at `p 4` disappears. -/
lemma halfLineIntegral_eq_Ioi_of_delta_zero
    (q : ℝ → ℝ) (p : HalfLineParam) (hAm : p 0 < p 4)
    (hdelta : p 3 = 0)
    (hint : IntegrableOn
      (fun x : ℝ ↦ q x * exp (p 1 + p 2 * x)) (Ioi (p 0))) :
    halfLineIntegral q p =
      ∫ x : ℝ in Ioi (p 0), q x * exp (p 1 + p 2 * x) := by
  have htail : IntegrableOn
      (fun x : ℝ ↦ q x * exp (p 1 + p 2 * x)) (Ioi (p 4)) :=
    hint.mono_set (Ioi_subset_Ioi hAm.le)
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint htail
  rw [halfLineIntegral, halfLineLeftIntegral, halfLineRightIntegral]
  change
    (∫ x : ℝ in p 0..p 4, q x * exp (p 1 + p 2 * x)) +
      (∫ x : ℝ in Ioi (p 4),
        q x * exp (p 1 + p 2 * x - p 3 * (x - p 4))) = _
  simp only [hdelta, zero_mul, sub_zero]
  exact hsplit

/-- Pulling the constant coefficient out of a decaying exponential ray. -/
lemma integrableOn_q_mul_exp_affine_Ioi
    (q : ℝ → ℝ) (A c beta : ℝ) (hbeta : beta < 0)
    (hq : IntegrableOn (fun x : ℝ ↦ q x * exp (beta * x)) (Ioi A)) :
    IntegrableOn (fun x : ℝ ↦ q x * exp (c + beta * x)) (Ioi A) := by
  have heq : (fun x : ℝ ↦ q x * exp (c + beta * x)) =
      fun x : ℝ ↦ exp c * (q x * exp (beta * x)) := by
    funext x
    rw [Real.exp_add]
    ring
  rw [heq]
  exact hq.const_mul (exp c)

private lemma exp_affine_right_change (A c lambda t : ℝ) (hlambda : lambda ≠ 0) :
    exp (c - lambda * (A + t / lambda)) =
      exp (c - lambda * A) * exp (-t) := by
  rw [← Real.exp_add]
  congr 1
  field_simp [hlambda]
  ring

/-- Zeroth moment of an exponential right ray. -/
lemma rightExp_mass (A c lambda : ℝ) (hlambda : 0 < lambda) :
    (∫ x : ℝ in Ioi A, exp (c - lambda * x)) =
      exp (c - lambda * A) / lambda := by
  rw [integral_Ioi_affine (fun x : ℝ ↦ exp (c - lambda * x)) A lambda hlambda]
  have hfun : (fun t : ℝ ↦ exp (c - lambda * (A + t / lambda))) =
      fun t : ℝ ↦ exp (c - lambda * A) * exp (-t) := by
    funext t
    exact exp_affine_right_change A c lambda t hlambda.ne'
  rw [hfun, MeasureTheory.integral_const_mul]
  rw [show (∫ t : ℝ in Ioi 0, exp (-t)) = 1 by
    simpa using (EndpointWitnesses.integral_exp_neg_mul_Ioi_zero
      (show (0 : ℝ) < 1 by norm_num))]
  field_simp [hlambda.ne']

/-- First moment of an exponential right ray. -/
lemma rightExp_mean (A c lambda : ℝ) (hlambda : 0 < lambda) :
    (∫ x : ℝ in Ioi A, x * exp (c - lambda * x)) =
      (exp (c - lambda * A) / lambda) * (A + 1 / lambda) := by
  rw [integral_Ioi_affine
    (fun x : ℝ ↦ x * exp (c - lambda * x)) A lambda hlambda]
  have hfun : (fun t : ℝ ↦
      (A + t / lambda) * exp (c - lambda * (A + t / lambda))) =
      fun t : ℝ ↦ exp (c - lambda * A) *
        (A * exp (-t) + (1 / lambda) * (t * exp (-t))) := by
    funext t
    rw [exp_affine_right_change A c lambda t hlambda.ne']
    field_simp [hlambda.ne']
  rw [hfun, MeasureTheory.integral_const_mul]
  have h0 : IntegrableOn (fun t : ℝ ↦ exp (-t)) (Ioi 0) := by
    simpa using integrableOn_exp_neg_Ioi 0
  have h1 : IntegrableOn (fun t : ℝ ↦ t * exp (-t)) (Ioi 0) := by
    simpa only [pow_one, neg_one_mul] using
      (EndpointWitnesses.integrableOn_pow_mul_exp_mul_Ioi
        1 (k := -1) (by norm_num) 0)
  rw [MeasureTheory.integral_add (h0.const_mul A) (h1.const_mul (1 / lambda)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [show (∫ t : ℝ in Ioi 0, exp (-t)) = 1 by
    simpa using (EndpointWitnesses.integral_exp_neg_mul_Ioi_zero
      (show (0 : ℝ) < 1 by norm_num))]
  rw [show (∫ t : ℝ in Ioi 0, t * exp (-t)) = 1 by
    simpa using (EndpointWitnesses.integral_mul_exp_neg_mul_Ioi_zero
      (show (0 : ℝ) < 1 by norm_num))]
  field_simp [hlambda.ne']

/-- Second moment of an exponential right ray. -/
lemma rightExp_second (A c lambda : ℝ) (hlambda : 0 < lambda) :
    (∫ x : ℝ in Ioi A, x ^ 2 * exp (c - lambda * x)) =
      (exp (c - lambda * A) / lambda) *
        (A ^ 2 + 2 * A / lambda + 2 / lambda ^ 2) := by
  rw [integral_Ioi_affine
    (fun x : ℝ ↦ x ^ 2 * exp (c - lambda * x)) A lambda hlambda]
  have hfun : (fun t : ℝ ↦
      (A + t / lambda) ^ 2 * exp (c - lambda * (A + t / lambda))) =
      fun t : ℝ ↦ exp (c - lambda * A) *
        ((A ^ 2 * exp (-t) + (2 * A / lambda) * (t * exp (-t))) +
          (1 / lambda ^ 2) * (t ^ 2 * exp (-t))) := by
    funext t
    rw [exp_affine_right_change A c lambda t hlambda.ne']
    field_simp [hlambda.ne']
    ring
  rw [hfun, MeasureTheory.integral_const_mul]
  have h0 : IntegrableOn (fun t : ℝ ↦ exp (-t)) (Ioi 0) := by
    simpa using integrableOn_exp_neg_Ioi 0
  have h1 : IntegrableOn (fun t : ℝ ↦ t * exp (-t)) (Ioi 0) := by
    simpa only [pow_one, neg_one_mul] using
      (EndpointWitnesses.integrableOn_pow_mul_exp_mul_Ioi
        1 (k := -1) (by norm_num) 0)
  have h2 : IntegrableOn (fun t : ℝ ↦ t ^ 2 * exp (-t)) (Ioi 0) := by
    simpa only [neg_one_mul] using
      (EndpointWitnesses.integrableOn_pow_mul_exp_mul_Ioi
        2 (k := -1) (by norm_num) 0)
  have hadd1 :
      (∫ t : ℝ in Ioi 0,
        A ^ 2 * exp (-t) + (2 * A / lambda) * (t * exp (-t))) =
        (∫ t : ℝ in Ioi 0, A ^ 2 * exp (-t)) +
          ∫ t : ℝ in Ioi 0, (2 * A / lambda) * (t * exp (-t)) := by
    exact MeasureTheory.integral_add (h0.const_mul (A ^ 2))
      (h1.const_mul (2 * A / lambda))
  have hadd2 :
      (∫ t : ℝ in Ioi 0,
        (A ^ 2 * exp (-t) + (2 * A / lambda) * (t * exp (-t))) +
          (1 / lambda ^ 2) * (t ^ 2 * exp (-t))) =
        (∫ t : ℝ in Ioi 0,
          A ^ 2 * exp (-t) + (2 * A / lambda) * (t * exp (-t))) +
          ∫ t : ℝ in Ioi 0, (1 / lambda ^ 2) * (t ^ 2 * exp (-t)) := by
    exact MeasureTheory.integral_add
      ((h0.const_mul (A ^ 2)).add (h1.const_mul (2 * A / lambda)))
      (h2.const_mul (1 / lambda ^ 2))
  rw [hadd2, hadd1, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [show (∫ t : ℝ in Ioi 0, exp (-t)) = 1 by
    simpa using (EndpointWitnesses.integral_exp_neg_mul_Ioi_zero
      (show (0 : ℝ) < 1 by norm_num))]
  rw [show (∫ t : ℝ in Ioi 0, t * exp (-t)) = 1 by
    simpa using (EndpointWitnesses.integral_mul_exp_neg_mul_Ioi_zero
      (show (0 : ℝ) < 1 by norm_num))]
  rw [show (∫ t : ℝ in Ioi 0, t ^ 2 * exp (-t)) = 2 by
    simpa using (EndpointWitnesses.integral_sq_mul_exp_neg_mul_Ioi_zero
      (show (0 : ℝ) < 1 by norm_num))]
  field_simp [hlambda.ne']

/-- An arbitrary test function under a right exponential ray. -/
lemma rightExp_test (q : ℝ → ℝ) (A c lambda : ℝ) (hlambda : 0 < lambda) :
    (∫ x : ℝ in Ioi A, q x * exp (c - lambda * x)) =
      (exp (c - lambda * A) / lambda) *
        ∫ t : ℝ in Ioi 0, q (A + t / lambda) * exp (-t) := by
  rw [integral_Ioi_affine
    (fun x : ℝ ↦ q x * exp (c - lambda * x)) A lambda hlambda]
  have hfun : (fun t : ℝ ↦
      q (A + t / lambda) * exp (c - lambda * (A + t / lambda))) =
      fun t : ℝ ↦ exp (c - lambda * A) *
        (q (A + t / lambda) * exp (-t)) := by
    funext t
    rw [exp_affine_right_change A c lambda t hlambda.ne']
    ring
  rw [hfun, MeasureTheory.integral_const_mul]
  ring

/-- Isotropy removes every free parameter from a zero-kink right-half-line
member of family (6).  The redundant split point `p 4` is intentionally not
mentioned in the conclusion. -/
lemma finiteLeft_terminal_parameters {p : HalfLineParam}
    (hadm : Admissible (.finiteLeft p))
    (hiso : IsIsotropic (.finiteLeft p)) (hdelta : p 3 = 0) :
    p 0 = -1 ∧ p 1 = -1 ∧ p 2 = -1 := by
  change p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0 at hadm
  have hbeta : p 2 < 0 := by linarith [hadm.2.2]
  have hlambda : 0 < -p 2 := by linarith
  have hmass0 : halfLineIntegral (fun _x : ℝ ↦ 1) p = 1 := by
    have h := congrFun hiso (0 : Fin 3)
    simpa [IsIsotropic, momentMap, integral, isotropicTarget] using h
  have hmean0 : halfLineIntegral (fun x : ℝ ↦ x) p = 0 := by
    have h := congrFun hiso (1 : Fin 3)
    simpa [IsIsotropic, momentMap, integral, isotropicTarget] using h
  have hsecond0 : halfLineIntegral (fun x : ℝ ↦ x ^ 2) p = 1 := by
    have h := congrFun hiso (2 : Fin 3)
    simpa [IsIsotropic, momentMap, integral, isotropicTarget] using h
  have hint0 : IntegrableOn
      (fun x : ℝ ↦ (1 : ℝ) * exp (p 1 + p 2 * x)) (Ioi (p 0)) := by
    apply integrableOn_q_mul_exp_affine_Ioi (fun _x : ℝ ↦ (1 : ℝ))
      (p 0) (p 1) (p 2) hbeta
    simpa only [pow_zero] using
      (LogConcaveClaimI.integrableOn_pow_mul_exp_mul_Ioi 0 hbeta (p 0))
  have hint1 : IntegrableOn
      (fun x : ℝ ↦ x * exp (p 1 + p 2 * x)) (Ioi (p 0)) := by
    apply integrableOn_q_mul_exp_affine_Ioi (fun x : ℝ ↦ x)
      (p 0) (p 1) (p 2) hbeta
    simpa only [pow_one] using
      (LogConcaveClaimI.integrableOn_pow_mul_exp_mul_Ioi 1 hbeta (p 0))
  have hint2 : IntegrableOn
      (fun x : ℝ ↦ x ^ 2 * exp (p 1 + p 2 * x)) (Ioi (p 0)) := by
    apply integrableOn_q_mul_exp_affine_Ioi (fun x : ℝ ↦ x ^ 2)
      (p 0) (p 1) (p 2) hbeta
    exact LogConcaveClaimI.integrableOn_pow_mul_exp_mul_Ioi 2 hbeta (p 0)
  have hmass :
      exp (p 1 - (-p 2) * p 0) / (-p 2) = 1 := by
    calc
      _ = ∫ x : ℝ in Ioi (p 0), exp (p 1 + p 2 * x) := by
        symm
        simpa only [neg_mul, sub_neg_eq_add] using
          (rightExp_mass (p 0) (p 1) (-p 2) hlambda)
      _ = halfLineIntegral (fun _x : ℝ ↦ 1) p := by
        symm
        simpa only [one_mul] using
          (halfLineIntegral_eq_Ioi_of_delta_zero
            (fun _x : ℝ ↦ (1 : ℝ)) p hadm.1 hdelta hint0)
      _ = 1 := hmass0
  have hmean :
      (exp (p 1 - (-p 2) * p 0) / (-p 2)) *
        (p 0 + 1 / (-p 2)) = 0 := by
    calc
      _ = ∫ x : ℝ in Ioi (p 0), x * exp (p 1 + p 2 * x) := by
        symm
        simpa only [neg_mul, sub_neg_eq_add] using
          (rightExp_mean (p 0) (p 1) (-p 2) hlambda)
      _ = halfLineIntegral (fun x : ℝ ↦ x) p := by
        symm
        exact halfLineIntegral_eq_Ioi_of_delta_zero
          (fun x : ℝ ↦ x) p hadm.1 hdelta hint1
      _ = 0 := hmean0
  have hsecond :
      (exp (p 1 - (-p 2) * p 0) / (-p 2)) *
        (p 0 ^ 2 + 2 * p 0 / (-p 2) + 2 / (-p 2) ^ 2) = 1 := by
    calc
      _ = ∫ x : ℝ in Ioi (p 0), x ^ 2 * exp (p 1 + p 2 * x) := by
        symm
        simpa only [neg_mul, sub_neg_eq_add] using
          (rightExp_second (p 0) (p 1) (-p 2) hlambda)
      _ = halfLineIntegral (fun x : ℝ ↦ x ^ 2) p := by
        symm
        exact halfLineIntegral_eq_Ioi_of_delta_zero
          (fun x : ℝ ↦ x ^ 2) p hadm.1 hdelta hint2
      _ = 1 := hsecond0
  rw [hmass] at hmean hsecond
  simp only [one_mul] at hmean hsecond
  have hA : p 0 = -(1 / (-p 2)) := by linarith
  rw [hA] at hsecond
  have hlambda_sq : (-p 2) ^ 2 = 1 := by
    norm_num at hsecond
    field_simp [hbeta.ne] at hsecond
    nlinarith
  have hlambda_one : -p 2 = 1 := by nlinarith
  have hp2 : p 2 = -1 := by linarith
  have hp0 : p 0 = -1 := by rw [hA, hlambda_one]; norm_num
  have hexp : exp (p 1 + 1) = 1 := by
    simpa [hp0, hp2] using hmass
  have hp1 : p 1 = -1 := by
    have := (Real.exp_eq_one_iff (p 1 + 1)).mp hexp
    linarith
  exact ⟨hp0, hp1, hp2⟩

/-- Every isotropic zero-kink member supported on a right half-line has the
centered one-sided-exponential value. -/
theorem finiteLeft_terminal_objective_eq_shifted
    {alpha : ℝ} (halpha : 0 ≤ alpha) {p : HalfLineParam}
    (hadm : Admissible (.finiteLeft p))
    (hiso : IsIsotropic (.finiteLeft p)) (hdelta : p 3 = 0) :
    objective alpha (.finiteLeft p) = shiftedValue alpha := by
  have hpar := finiteLeft_terminal_parameters hadm hiso hdelta
  rcases hpar with ⟨hp0, hp1, hp2⟩
  have hadm' := hadm
  change p 0 < p 4 ∧ 0 ≤ p 3 ∧ p 2 - p 3 < 0 at hadm'
  have hbase : IntegrableOn
      (fun x : ℝ ↦ LogConcaveClaimI.gAlpha alpha x * exp ((-1 : ℝ) * x))
        (Ioi (-1)) := by
    simpa only [pow_zero, one_mul] using
      (LogConcaveClaimI.integrableOn_pow_mul_gAlpha_mul_exp_mul_Ioi
        0 halpha (show (-1 : ℝ) < 0 by norm_num) (-1))
  have hint : IntegrableOn
      (fun x : ℝ ↦ LogConcaveClaimI.gAlpha alpha x *
        exp ((-1 : ℝ) + (-1) * x))
        (Ioi (-1)) :=
    integrableOn_q_mul_exp_affine_Ioi (LogConcaveClaimI.gAlpha alpha)
      (-1) (-1) (-1)
      (by norm_num) hbase
  have hcollapse := halfLineIntegral_eq_Ioi_of_delta_zero
    (LogConcaveClaimI.gAlpha alpha) p hadm'.1 hdelta
      (by simpa [hp0, hp1, hp2] using hint)
  calc
    objective alpha (.finiteLeft p) =
        ∫ x : ℝ in Ioi (-1),
          LogConcaveClaimI.gAlpha alpha x * exp ((-1 : ℝ) + (-1) * x) := by
      change halfLineIntegral (LogConcaveClaimI.gAlpha alpha) p = _
      simpa [hp0, hp1, hp2] using hcollapse
    _ = ∫ t : ℝ in Ioi 0,
        _root_.gAlpha alpha |1 - t| * exp (-t) := by
      rw [integral_Ioi_affine
        (fun x : ℝ ↦ LogConcaveClaimI.gAlpha alpha x *
          exp ((-1 : ℝ) + (-1) * x))
        (-1) 1 (by norm_num)]
      simp only [inv_one, one_mul, div_one]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t _ht
      unfold LogConcaveClaimI.gAlpha _root_.gAlpha
      have habs : |-1 + t| = |1 - t| := by
        rw [show -1 + t = -(1 - t) by ring, abs_neg]
      change
        (1 + alpha * |-1 + t|) * exp (-alpha * |-1 + t|) *
            exp (-1 + -1 * (-1 + t)) =
          (1 + alpha * |1 - t|) * exp (-alpha * |1 - t|) * exp (-t)
      rw [habs]
      congr 2
      ring
    _ = asymLaplaceObjective alpha 1 0 := by
      simp [asymLaplaceObjective]
    _ = shiftedValue alpha := asymLaplaceObjective_shifted alpha halpha

/-- Reflection transfers the preceding normalization to a left half-line. -/
theorem finiteRight_terminal_objective_eq_shifted
    {alpha : ℝ} (halpha : 0 ≤ alpha) {p : HalfLineParam}
    (hadm : Admissible (.finiteRight p))
    (hiso : IsIsotropic (.finiteRight p)) (hdelta : p 3 = 0) :
    objective alpha (.finiteRight p) = shiftedValue alpha := by
  let pr : HalfLineParam := LogConcaveClaimI.halfLineReflect p
  have hadmR : Admissible (.finiteLeft pr) := by
    change pr 0 < pr 4 ∧ 0 ≤ pr 3 ∧ pr 2 - pr 3 < 0
    change p 4 < p 0 ∧ 0 ≤ p 3 ∧ 0 < p 2 at hadm
    dsimp [pr]
    simp only [LogConcaveClaimI.halfLineReflect_zero,
      LogConcaveClaimI.halfLineReflect_two,
      LogConcaveClaimI.halfLineReflect_three,
      LogConcaveClaimI.halfLineReflect_four]
    constructor
    · linarith [hadm.1]
    · exact ⟨hadm.2.1, by linarith [hadm.2.2]⟩
  have hisoR : IsIsotropic (.finiteLeft pr) := by
    have hiso' := hiso
    change LogConcaveClaimI.finiteRightActualMomentMap p = isotropicTarget at hiso'
    rw [LogConcaveClaimI.finiteRightActualMomentMap_eq] at hiso'
    change LogConcaveClaimI.halfLineMomentMap pr = isotropicTarget
    funext k
    have hk := congrFun hiso' k
    fin_cases k <;>
      norm_num [LogConcaveClaimI.finiteRightMomentMap, isotropicTarget] at hk ⊢ <;>
      linarith
  have hdeltaR : pr 3 = 0 := by
    dsimp [pr]
    simpa using hdelta
  have hR := finiteLeft_terminal_objective_eq_shifted halpha hadmR hisoR hdeltaR
  change LogConcaveClaimI.finiteRightActualIntegral
      (LogConcaveClaimI.gAlpha alpha) p = shiftedValue alpha
  rw [LogConcaveClaimI.finiteRightActualIntegral_eq_reflect]
  have heven : (fun x : ℝ ↦ LogConcaveClaimI.gAlpha alpha (-x)) =
      LogConcaveClaimI.gAlpha alpha := by
    funext x
    exact LogConcaveClaimI.gAlpha_neg alpha x
  rw [heven]
  exact hR

/-! ## Two exponential rays on the whole line -/

lemma leftExp_mass (m c lambda : ℝ) (hlambda : 0 < lambda) :
    (∫ x : ℝ in Iic m, exp (c + lambda * x)) =
      exp (c + lambda * m) / lambda := by
  rw [integral_Iic_eq_Ioi_reflect]
  simpa only [mul_neg, sub_eq_add_neg, neg_neg] using
    (rightExp_mass (-m) c lambda hlambda)

lemma leftExp_mean (m c lambda : ℝ) (hlambda : 0 < lambda) :
    (∫ x : ℝ in Iic m, x * exp (c + lambda * x)) =
      (exp (c + lambda * m) / lambda) * (m - 1 / lambda) := by
  rw [integral_Iic_eq_Ioi_reflect]
  have hfun : (fun y : ℝ ↦ (-y) * exp (c + lambda * (-y))) =
      fun y : ℝ ↦ -(y * exp (c - lambda * y)) := by
    funext y
    congr 2 <;> ring_nf
  rw [hfun, MeasureTheory.integral_neg,
    rightExp_mean (-m) c lambda hlambda]
  ring_nf

lemma leftExp_second (m c lambda : ℝ) (hlambda : 0 < lambda) :
    (∫ x : ℝ in Iic m, x ^ 2 * exp (c + lambda * x)) =
      (exp (c + lambda * m) / lambda) *
        (m ^ 2 - 2 * m / lambda + 2 / lambda ^ 2) := by
  rw [integral_Iic_eq_Ioi_reflect]
  have hfun : (fun y : ℝ ↦ (-y) ^ 2 * exp (c + lambda * (-y))) =
      fun y : ℝ ↦ y ^ 2 * exp (c - lambda * y) := by
    funext y
    rw [show (-y) ^ 2 = y ^ 2 by ring]
    congr 2
    ring
  rw [hfun, rightExp_second (-m) c lambda hlambda]
  ring_nf

/-- An arbitrary test function under a left exponential ray. -/
lemma leftExp_test (q : ℝ → ℝ) (m c lambda : ℝ) (hlambda : 0 < lambda) :
    (∫ x : ℝ in Iic m, q x * exp (c + lambda * x)) =
      (exp (c + lambda * m) / lambda) *
        ∫ t : ℝ in Ioi 0, q (m - t / lambda) * exp (-t) := by
  rw [integral_Iic_affine
    (fun x : ℝ ↦ q x * exp (c + lambda * x)) m lambda hlambda]
  have hfun : (fun t : ℝ ↦
      q (m - t / lambda) * exp (c + lambda * (m - t / lambda))) =
      fun t : ℝ ↦ exp (c + lambda * m) *
        (q (m - t / lambda) * exp (-t)) := by
    funext t
    have hexp : exp (c + lambda * (m - t / lambda)) =
        exp (c + lambda * m) * exp (-t) := by
      rw [← Real.exp_add]
      congr 1
      field_simp [hlambda.ne']
      ring
    rw [hexp]
    ring
  rw [hfun, MeasureTheory.integral_const_mul]
  ring

private lemma wholeLine_right_exponent_eq (p : WholeLineParam) (x : ℝ) :
    p.c + p.beta * x - p.delta * (x - p.m) =
      (p.c + p.delta * p.m) - (p.delta - p.beta) * x := by
  ring

/-- The three raw moments of a whole-line family-(6) density, expressed by
the common height at the kink and its two decay rates. -/
lemma wholeLine_moment_formulas (p : WholeLineParam)
    (hbeta : 0 < p.beta) (hgamma : 0 < p.delta - p.beta) :
    integral (fun _x : ℝ ↦ 1) (.wholeLine p) =
        exp (p.c + p.beta * p.m) / p.beta +
          exp (p.c + p.beta * p.m) / (p.delta - p.beta) ∧
    integral (fun x : ℝ ↦ x) (.wholeLine p) =
        (exp (p.c + p.beta * p.m) / p.beta) *
            (p.m - 1 / p.beta) +
          (exp (p.c + p.beta * p.m) / (p.delta - p.beta)) *
            (p.m + 1 / (p.delta - p.beta)) ∧
    integral (fun x : ℝ ↦ x ^ 2) (.wholeLine p) =
        (exp (p.c + p.beta * p.m) / p.beta) *
            (p.m ^ 2 - 2 * p.m / p.beta + 2 / p.beta ^ 2) +
          (exp (p.c + p.beta * p.m) / (p.delta - p.beta)) *
            (p.m ^ 2 + 2 * p.m / (p.delta - p.beta) +
              2 / (p.delta - p.beta) ^ 2) := by
  have hr0 :
      (∫ x : ℝ in Ioi p.m,
        exp (p.c + p.beta * x - p.delta * (x - p.m))) =
        exp (p.c + p.beta * p.m) / (p.delta - p.beta) := by
    calc
      _ = ∫ x : ℝ in Ioi p.m,
          exp ((p.c + p.delta * p.m) - (p.delta - p.beta) * x) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x _hx
        change exp (p.c + p.beta * x - p.delta * (x - p.m)) =
          exp ((p.c + p.delta * p.m) - (p.delta - p.beta) * x)
        rw [wholeLine_right_exponent_eq]
      _ = _ := by
        convert rightExp_mass p.m (p.c + p.delta * p.m)
          (p.delta - p.beta) hgamma using 1
        congr 2
        ring_nf
  have hr1 :
      (∫ x : ℝ in Ioi p.m,
        x * exp (p.c + p.beta * x - p.delta * (x - p.m))) =
        (exp (p.c + p.beta * p.m) / (p.delta - p.beta)) *
          (p.m + 1 / (p.delta - p.beta)) := by
    calc
      _ = ∫ x : ℝ in Ioi p.m,
          x * exp ((p.c + p.delta * p.m) - (p.delta - p.beta) * x) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x _hx
        change x * exp (p.c + p.beta * x - p.delta * (x - p.m)) =
          x * exp ((p.c + p.delta * p.m) - (p.delta - p.beta) * x)
        rw [wholeLine_right_exponent_eq]
      _ = _ := by
        convert rightExp_mean p.m (p.c + p.delta * p.m)
          (p.delta - p.beta) hgamma using 1
        congr 2
        ring_nf
  have hr2 :
      (∫ x : ℝ in Ioi p.m,
        x ^ 2 * exp (p.c + p.beta * x - p.delta * (x - p.m))) =
        (exp (p.c + p.beta * p.m) / (p.delta - p.beta)) *
          (p.m ^ 2 + 2 * p.m / (p.delta - p.beta) +
            2 / (p.delta - p.beta) ^ 2) := by
    calc
      _ = ∫ x : ℝ in Ioi p.m,
          x ^ 2 * exp ((p.c + p.delta * p.m) -
            (p.delta - p.beta) * x) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x _hx
        change x ^ 2 * exp (p.c + p.beta * x - p.delta * (x - p.m)) =
          x ^ 2 * exp ((p.c + p.delta * p.m) - (p.delta - p.beta) * x)
        rw [wholeLine_right_exponent_eq]
      _ = _ := by
        convert rightExp_second p.m (p.c + p.delta * p.m)
          (p.delta - p.beta) hgamma using 1
        congr 2
        ring_nf
  constructor
  · simp only [integral, one_mul]
    rw [leftExp_mass p.m p.c p.beta hbeta, hr0]
  constructor
  · simp only [integral]
    rw [leftExp_mean p.m p.c p.beta hbeta, hr1]
  · change
      (∫ x : ℝ in Iic p.m, x ^ 2 * exp (p.c + p.beta * x)) +
        (∫ x : ℝ in Ioi p.m,
          x ^ 2 * exp (p.c + p.beta * x - p.delta * (x - p.m))) = _
    rw [leftExp_second p.m p.c p.beta hbeta, hr2]

/-- Isotropy identifies every admissible whole-line member with a normalized
asymmetric-Laplace pair. -/
theorem wholeLine_isotropic_normal_form {p : WholeLineParam}
    (hadm : Admissible (.wholeLine p))
    (hiso : IsIsotropic (.wholeLine p)) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = 1 ∧
      a = 1 / p.beta ∧ b = 1 / (p.delta - p.beta) ∧
      p.m = a - b ∧ exp (p.c + p.beta * p.m) = 1 / (a + b) := by
  change 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0 at hadm
  have hbeta : 0 < p.beta := hadm.2.1
  have hgamma : 0 < p.delta - p.beta := by linarith [hadm.2.2]
  let a : ℝ := 1 / p.beta
  let b : ℝ := 1 / (p.delta - p.beta)
  let H : ℝ := exp (p.c + p.beta * p.m)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hmass0 : integral (fun _x : ℝ ↦ 1) (.wholeLine p) = 1 := by
    have h := congrFun hiso (0 : Fin 3)
    simpa [IsIsotropic, momentMap, isotropicTarget] using h
  have hmean0 : integral (fun x : ℝ ↦ x) (.wholeLine p) = 0 := by
    have h := congrFun hiso (1 : Fin 3)
    simpa [IsIsotropic, momentMap, isotropicTarget] using h
  have hsecond0 : integral (fun x : ℝ ↦ x ^ 2) (.wholeLine p) = 1 := by
    have h := congrFun hiso (2 : Fin 3)
    simpa [IsIsotropic, momentMap, isotropicTarget] using h
  rcases wholeLine_moment_formulas p hbeta hgamma with
    ⟨hmassF, hmeanF, hsecondF⟩
  have hmass : H * a + H * b = 1 := by
    calc
      H * a + H * b = integral (fun _x : ℝ ↦ 1) (.wholeLine p) := by
        rw [hmassF]
        simp only [H, a, b, div_eq_mul_inv, one_mul]
      _ = 1 := hmass0
  have hmean : H * a * (p.m - a) + H * b * (p.m + b) = 0 := by
    calc
      _ = integral (fun x : ℝ ↦ x) (.wholeLine p) := by
        rw [hmeanF]
        simp only [H, a, b, div_eq_mul_inv, one_mul]
      _ = 0 := hmean0
  have hsecond :
      H * a * (p.m ^ 2 - 2 * p.m * a + 2 * a ^ 2) +
        H * b * (p.m ^ 2 + 2 * p.m * b + 2 * b ^ 2) = 1 := by
    calc
      _ = integral (fun x : ℝ ↦ x ^ 2) (.wholeLine p) := by
        rw [hsecondF]
        simp only [H, a, b, div_eq_mul_inv, one_mul, inv_pow]
      _ = 1 := hsecond0
  have hmass' : H * (a + b) = 1 := by linarith [hmass]
  have hmeanRewrite :
      H * a * (p.m - a) + H * b * (p.m + b) =
        H * (a + b) * (p.m - a + b) := by ring
  rw [hmeanRewrite, hmass'] at hmean
  have hm : p.m = a - b := by linarith
  have hsecondRewrite :
      H * a * ((a - b) ^ 2 - 2 * (a - b) * a + 2 * a ^ 2) +
          H * b * ((a - b) ^ 2 + 2 * (a - b) * b + 2 * b ^ 2) =
        H * (a + b) * (a ^ 2 + b ^ 2) := by ring
  rw [hm, hsecondRewrite, hmass'] at hsecond
  have hnorm : a ^ 2 + b ^ 2 = 1 := by simpa using hsecond
  have habne : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hH : H = 1 / (a + b) := by
    apply (eq_div_iff habne).2
    simpa [one_mul] using hmass'
  exact ⟨a, b, ha, hb, hnorm, rfl, rfl, hm, hH⟩

/-- The objective of an isotropic whole-line member is exactly the normalized
asymmetric-Laplace objective used in Claim (iii). -/
theorem wholeLine_terminal_objective_eq_asymLaplace
    (alpha : ℝ) {p : WholeLineParam}
    (hadm : Admissible (.wholeLine p))
    (hiso : IsIsotropic (.wholeLine p)) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a ^ 2 + b ^ 2 = 1 ∧
      objective alpha (.wholeLine p) = asymLaplaceObjective alpha a b := by
  rcases wholeLine_isotropic_normal_form hadm hiso with
    ⟨a, b, ha, hb, hnorm, haDef, hbDef, hm, hH⟩
  have hadm' := hadm
  change 0 ≤ p.delta ∧ 0 < p.beta ∧ p.beta - p.delta < 0 at hadm'
  have hbeta : 0 < p.beta := hadm'.2.1
  have hgamma : 0 < p.delta - p.beta := by linarith [hadm'.2.2]
  have hinvBeta : p.beta⁻¹ = a := by
    simpa only [one_div] using haDef.symm
  have hinvGamma : (p.delta - p.beta)⁻¹ = b := by
    simpa only [one_div] using hbDef.symm
  have hcoefL : exp (p.c + p.beta * p.m) / p.beta = a / (a + b) := by
    rw [hH]
    simp only [div_eq_mul_inv, hinvBeta]
    ring
  have hheightR :
      exp ((p.c + p.delta * p.m) - (p.delta - p.beta) * p.m) =
        exp (p.c + p.beta * p.m) := by
    congr 1
    ring
  have hcoefR :
      exp ((p.c + p.delta * p.m) - (p.delta - p.beta) * p.m) /
          (p.delta - p.beta) = b / (a + b) := by
    rw [hheightR, hH]
    simp only [div_eq_mul_inv, hinvGamma]
    ring
  have hargL (t : ℝ) : p.m - t / p.beta = (a - b) - a * t := by
    rw [hm]
    simp only [div_eq_mul_inv, hinvBeta]
    ring
  have hargR (t : ℝ) : p.m + t / (p.delta - p.beta) =
      (a - b) + b * t := by
    rw [hm]
    simp only [div_eq_mul_inv, hinvGamma]
    ring
  have hg (x : ℝ) : LogConcaveClaimI.gAlpha alpha x =
      _root_.gAlpha alpha |x| := by
    simp [LogConcaveClaimI.gAlpha, _root_.gAlpha]
  have hleft :
      (∫ x : ℝ in Iic p.m,
        LogConcaveClaimI.gAlpha alpha x * exp (p.c + p.beta * x)) =
        a / (a + b) *
          ∫ t : ℝ in Ioi 0,
            _root_.gAlpha alpha |(a - b) - a * t| * exp (-t) := by
    rw [leftExp_test (LogConcaveClaimI.gAlpha alpha)
      p.m p.c p.beta hbeta, hcoefL]
    apply congrArg (fun z : ℝ ↦ a / (a + b) * z)
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _ht
    change LogConcaveClaimI.gAlpha alpha (p.m - t / p.beta) * exp (-t) =
      _root_.gAlpha alpha |(a - b) - a * t| * exp (-t)
    rw [hargL, hg]
  have hright :
      (∫ x : ℝ in Ioi p.m,
        LogConcaveClaimI.gAlpha alpha x *
          exp (p.c + p.beta * x - p.delta * (x - p.m))) =
        b / (a + b) *
          ∫ t : ℝ in Ioi 0,
            _root_.gAlpha alpha |(a - b) + b * t| * exp (-t) := by
    calc
      _ = ∫ x : ℝ in Ioi p.m,
          LogConcaveClaimI.gAlpha alpha x *
            exp ((p.c + p.delta * p.m) - (p.delta - p.beta) * x) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro x _hx
        change LogConcaveClaimI.gAlpha alpha x *
            exp (p.c + p.beta * x - p.delta * (x - p.m)) =
          LogConcaveClaimI.gAlpha alpha x *
            exp ((p.c + p.delta * p.m) - (p.delta - p.beta) * x)
        rw [wholeLine_right_exponent_eq]
      _ = exp ((p.c + p.delta * p.m) - (p.delta - p.beta) * p.m) /
            (p.delta - p.beta) *
          (∫ t : ℝ in Ioi 0,
            LogConcaveClaimI.gAlpha alpha
                (p.m + t / (p.delta - p.beta)) * exp (-t)) :=
        rightExp_test (LogConcaveClaimI.gAlpha alpha) p.m
          (p.c + p.delta * p.m) (p.delta - p.beta) hgamma
      _ = _ := by
        rw [hcoefR]
        apply congrArg (fun z : ℝ ↦ b / (a + b) * z)
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro t _ht
        change LogConcaveClaimI.gAlpha alpha
              (p.m + t / (p.delta - p.beta)) * exp (-t) =
          _root_.gAlpha alpha |(a - b) + b * t| * exp (-t)
        rw [hargR, hg]
  refine ⟨a, b, ha.le, hb.le, hnorm, ?_⟩
  change
    (∫ x : ℝ in Iic p.m,
      LogConcaveClaimI.gAlpha alpha x * exp (p.c + p.beta * x)) +
      (∫ x : ℝ in Ioi p.m,
        LogConcaveClaimI.gAlpha alpha x *
          exp (p.c + p.beta * x - p.delta * (x - p.m))) = _
  rw [hleft, hright]
  rfl

/-! ## Claim (iii) for the tagged terminal family -/

/-- All terminal shapes in family (6) satisfy the sharp Claim-(iii) bound. -/
theorem terminal_objective_le_max
    {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    {theta : Param} (htheta : theta ∈ family6)
    (hterminal : TerminalShape theta) :
    objective alpha theta ≤
      max (shiftedValue alpha) (laplaceValue alpha) := by
  rcases htheta with ⟨hadm, hiso⟩
  cases theta with
  | compact p =>
      exact hterminal.elim
  | finiteLeft p =>
      have heq := finiteLeft_terminal_objective_eq_shifted
        halpha.le hadm hiso hterminal
      rw [heq]
      exact le_max_left _ _
  | finiteRight p =>
      have heq := finiteRight_terminal_objective_eq_shifted
        halpha.le hadm hiso hterminal
      rw [heq]
      exact le_max_left _ _
  | wholeLine p =>
      rcases wholeLine_terminal_objective_eq_asymLaplace alpha hadm hiso with
        ⟨a, b, ha, hb, hab, heq⟩
      rw [heq]
      exact AsymLaplaceAssembly.asymLaplaceObjective_le_max
        halpha halpha1 ha hb hab

end LogConcaveFamily6

end FlattenedExistenceSection20


/-!
Flattened source section: Family6EndpointParams.lean
-/

section FlattenedExistenceSection21

open Real Set MeasureTheory

namespace LogConcaveFamily6.EndpointParams

open LogConcaveClaimI

/-! ## The centered one-sided exponential as an actual tagged parameter -/

def shiftedHalfLineParam : HalfLineParam := ![-1, -1, -1, 0, 0]

@[simp] lemma shiftedHalfLineParam_zero : shiftedHalfLineParam 0 = -1 := rfl
@[simp] lemma shiftedHalfLineParam_one : shiftedHalfLineParam 1 = -1 := rfl
@[simp] lemma shiftedHalfLineParam_two : shiftedHalfLineParam 2 = -1 := rfl
@[simp] lemma shiftedHalfLineParam_three : shiftedHalfLineParam 3 = 0 := rfl
@[simp] lemma shiftedHalfLineParam_four : shiftedHalfLineParam 4 = 0 := rfl

def shiftedParam : Param := .finiteLeft shiftedHalfLineParam

lemma shifted_admissible : Admissible shiftedParam := by
  change (-1 : ℝ) < 0 ∧ 0 ≤ 0 ∧ (-1 : ℝ) - 0 < 0
  norm_num

private lemma shifted_integrable (n : ℕ) :
    IntegrableOn
      (fun x : ℝ ↦ x ^ n * exp ((-1 : ℝ) + (-1) * x)) (Ioi (-1)) := by
  apply integrableOn_q_mul_exp_affine_Ioi (fun x : ℝ ↦ x ^ n)
    (-1) (-1) (-1) (by norm_num)
  exact LogConcaveClaimI.integrableOn_pow_mul_exp_mul_Ioi n (by norm_num) (-1)

lemma shifted_mass : integral (fun _ : ℝ ↦ 1) shiftedParam = 1 := by
  have hcollapse := halfLineIntegral_eq_Ioi_of_delta_zero
    (fun _ : ℝ ↦ 1) shiftedHalfLineParam
      (by rw [shiftedHalfLineParam_zero, shiftedHalfLineParam_four]; norm_num)
      (by rfl)
      (by simpa only [shiftedHalfLineParam_zero, shiftedHalfLineParam_one,
        shiftedHalfLineParam_two, pow_zero, one_mul] using shifted_integrable 0)
  change halfLineIntegral (fun _ : ℝ ↦ 1) shiftedHalfLineParam = 1
  rw [hcollapse]
  simp only [shiftedHalfLineParam_zero, shiftedHalfLineParam_one,
    shiftedHalfLineParam_two, one_mul]
  calc
    (∫ x : ℝ in Ioi (-1), exp (-1 + -1 * x)) =
        ∫ x : ℝ in Ioi (-1), exp (-1 - 1 * x) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      congr 1
      ring_nf
    _ = 1 := by simpa using rightExp_mass (-1) (-1) 1 (by norm_num)

lemma shifted_mean : integral (fun x : ℝ ↦ x) shiftedParam = 0 := by
  have hcollapse := halfLineIntegral_eq_Ioi_of_delta_zero
    (fun x : ℝ ↦ x) shiftedHalfLineParam
      (by rw [shiftedHalfLineParam_zero, shiftedHalfLineParam_four]; norm_num)
      (by rfl)
      (by simpa only [shiftedHalfLineParam_zero, shiftedHalfLineParam_one,
        shiftedHalfLineParam_two, pow_one] using shifted_integrable 1)
  change halfLineIntegral (fun x : ℝ ↦ x) shiftedHalfLineParam = 0
  rw [hcollapse]
  simp only [shiftedHalfLineParam_zero, shiftedHalfLineParam_one,
    shiftedHalfLineParam_two]
  calc
    (∫ x : ℝ in Ioi (-1), x * exp (-1 + -1 * x)) =
        ∫ x : ℝ in Ioi (-1), x * exp (-1 - 1 * x) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      congr 2
      ring_nf
    _ = 0 := by simpa using rightExp_mean (-1) (-1) 1 (by norm_num)

lemma shifted_second : integral (fun x : ℝ ↦ x ^ 2) shiftedParam = 1 := by
  have hcollapse := halfLineIntegral_eq_Ioi_of_delta_zero
    (fun x : ℝ ↦ x ^ 2) shiftedHalfLineParam
      (by rw [shiftedHalfLineParam_zero, shiftedHalfLineParam_four]; norm_num)
      (by rfl)
      (by simpa only [shiftedHalfLineParam_zero, shiftedHalfLineParam_one,
        shiftedHalfLineParam_two] using shifted_integrable 2)
  change halfLineIntegral (fun x : ℝ ↦ x ^ 2) shiftedHalfLineParam = 1
  rw [hcollapse]
  simp only [shiftedHalfLineParam_zero, shiftedHalfLineParam_one,
    shiftedHalfLineParam_two]
  calc
    (∫ x : ℝ in Ioi (-1), x ^ 2 * exp (-1 + -1 * x)) =
        ∫ x : ℝ in Ioi (-1), x ^ 2 * exp (-1 - 1 * x) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x _hx
      congr 2
      ring_nf
    _ = 1 := by simpa using rightExp_second (-1) (-1) 1 (by norm_num)

lemma shifted_isIsotropic : IsIsotropic shiftedParam := by
  funext k
  fin_cases k
  · simpa [IsIsotropic, momentMap, isotropicTarget] using shifted_mass
  · simpa [IsIsotropic, momentMap, isotropicTarget] using shifted_mean
  · simpa [IsIsotropic, momentMap, isotropicTarget] using shifted_second

theorem shifted_mem_family6 : shiftedParam ∈ family6 :=
  ⟨shifted_admissible, shifted_isIsotropic⟩

lemma shiftedValue_eq_S (alpha : ℝ) (halpha : 0 ≤ alpha) :
    shiftedValue alpha = S alpha := by
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun x : ℝ ↦ (1 + alpha * x) * exp ((1 - alpha) * x))
    (a := (0 : ℝ)) (b := 1) 1
  have hsub' :
      (∫ x : ℝ in 0..1,
        (1 + alpha * (1 - x)) * exp ((1 - alpha) * (1 - x))) =
      ∫ x : ℝ in 0..1,
        (1 + alpha * x) * exp ((1 - alpha) * x) := by
    simpa only [sub_self, sub_zero] using hsub
  have hfinite :
      exp (-alpha) *
          (∫ t : ℝ in 0..1,
            (1 + alpha - alpha * t) * exp (-(1 - alpha) * t)) =
        exp (-1) *
          (∫ x : ℝ in 0..1,
            (1 + alpha * x) * exp ((1 - alpha) * x)) := by
    rw [← hsub']
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    have hcoeff : 1 + alpha * (1 - t) = 1 + alpha - alpha * t := by ring
    have hexp :
        exp (-alpha) * exp (-(1 - alpha) * t) =
          exp (-1) * exp ((1 - alpha) * (1 - t)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    change
      exp (-alpha) *
          ((1 + alpha - alpha * t) * exp (-(1 - alpha) * t)) =
        exp (-1) *
          ((1 + alpha * (1 - t)) * exp ((1 - alpha) * (1 - t)))
    rw [hcoeff]
    calc
      exp (-alpha) *
          ((1 + alpha - alpha * t) * exp (-(1 - alpha) * t)) =
          (1 + alpha - alpha * t) *
            (exp (-alpha) * exp (-(1 - alpha) * t)) := by ring
      _ = (1 + alpha - alpha * t) *
            (exp (-1) * exp ((1 - alpha) * (1 - t))) := by rw [hexp]
      _ = exp (-1) *
          ((1 + alpha - alpha * t) * exp ((1 - alpha) * (1 - t))) := by ring
  rw [← asymLaplaceObjective_shifted alpha halpha,
    asymLaplaceObjective_shifted_split alpha halpha]
  unfold S
  rw [hfinite]
  ring

theorem shifted_objective (alpha : ℝ) (halpha : 0 ≤ alpha) :
    objective alpha shiftedParam = S alpha := by
  change objective alpha (.finiteLeft shiftedHalfLineParam) = S alpha
  rw [finiteLeft_terminal_objective_eq_shifted halpha shifted_admissible
    shifted_isIsotropic (by rfl)]
  exact shiftedValue_eq_S alpha halpha

/-- The centered one-sided exponential is an actual member of the tagged
family and realizes the value `S alpha`. -/
theorem exists_shifted_witness (alpha : ℝ) (halpha : 0 ≤ alpha) :
    ∃ p ∈ family6, objective alpha p = S alpha :=
  ⟨shiftedParam, shifted_mem_family6, shifted_objective alpha halpha⟩

/-! ## The symmetric Laplace law as an actual tagged parameter -/

def laplaceWholeLineParam : WholeLineParam where
  c := log (1 / sqrt 2)
  beta := sqrt 2
  delta := 2 * sqrt 2
  m := 0

def laplaceParam : Param := .wholeLine laplaceWholeLineParam

lemma laplace_admissible : Admissible laplaceParam := by
  change 0 ≤ 2 * sqrt 2 ∧ 0 < sqrt 2 ∧ sqrt 2 - 2 * sqrt 2 < 0
  constructor
  · positivity
  constructor
  · exact EndpointWitnesses.sqrt_two_pos
  · linarith [EndpointWitnesses.sqrt_two_pos]

lemma laplace_realDensity (x : ℝ) :
    Law.realDensity laplaceParam x = EndpointWitnesses.laplaceDensity x := by
  change
    (Iic (0 : ℝ)).indicator
        (fun y ↦ exp (log (1 / sqrt 2) + sqrt 2 * y)) x +
      (Ioi (0 : ℝ)).indicator
        (fun y ↦ exp (log (1 / sqrt 2) + sqrt 2 * y -
          2 * sqrt 2 * (y - 0))) x =
      (1 / sqrt 2) * exp (-(sqrt 2 * |x|))
  by_cases hx : x ≤ 0
  · have hnot : x ∉ Ioi (0 : ℝ) := by simpa [mem_Ioi] using hx
    rw [Set.indicator_of_mem (show x ∈ Iic (0 : ℝ) by exact hx),
      Set.indicator_of_notMem hnot, add_zero, abs_of_nonpos hx]
    rw [show -(sqrt 2 * -x) = sqrt 2 * x by ring,
      Real.exp_add,
      Real.exp_log (by positivity : 0 < (1 / sqrt (2 : ℝ)))]
  · have hx0 : 0 < x := lt_of_not_ge hx
    have hnot : x ∉ Iic (0 : ℝ) := by simpa [mem_Iic] using hx
    rw [Set.indicator_of_notMem hnot,
      Set.indicator_of_mem (show x ∈ Ioi (0 : ℝ) by exact hx0), zero_add,
      abs_of_pos hx0]
    rw [show log (1 / sqrt 2) + sqrt 2 * x -
        2 * sqrt 2 * (x - 0) =
        log (1 / sqrt 2) + (-(sqrt 2 * x)) by ring,
      Real.exp_add,
      Real.exp_log (by positivity : 0 < (1 / sqrt (2 : ℝ)))]

private lemma laplace_integral_eq (q : ℝ → ℝ)
    (hq : Law.PieceIntegrable laplaceParam q) :
    integral q laplaceParam =
      ∫ x : ℝ, q x * EndpointWitnesses.laplaceDensity x := by
  rw [← Law.integral_against_realDensity laplace_admissible q hq]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [laplace_realDensity]
  ring

lemma laplace_mass : integral (fun _ : ℝ ↦ 1) laplaceParam = 1 := by
  rw [laplace_integral_eq (fun _ : ℝ ↦ 1)
    (Law.pieceIntegrable_one laplace_admissible)]
  simpa using EndpointWitnesses.laplace_mass

lemma laplace_second : integral (fun x : ℝ ↦ x ^ 2) laplaceParam = 1 := by
  rw [laplace_integral_eq (fun x : ℝ ↦ x ^ 2)
    (Law.pieceIntegrable_sq laplace_admissible)]
  exact EndpointWitnesses.laplace_second_moment

lemma laplace_mean : integral (fun x : ℝ ↦ x) laplaceParam = 0 := by
  change
    (∫ x : ℝ in Iic 0,
      x * exp (log (1 / sqrt 2) + sqrt 2 * x)) +
    (∫ x : ℝ in Ioi 0,
      x * exp (log (1 / sqrt 2) + sqrt 2 * x -
        2 * sqrt 2 * (x - 0))) = 0
  rw [integral_Iic_eq_Ioi_reflect]
  simp only [neg_zero]
  have hleft : (fun y : ℝ ↦
      (-y) * exp (log (1 / sqrt 2) + sqrt 2 * (-y))) =
      fun y : ℝ ↦ -(y * exp (log (1 / sqrt 2) - sqrt 2 * y)) := by
    funext y
    rw [show log (1 / sqrt 2) + sqrt 2 * (-y) =
        log (1 / sqrt 2) - sqrt 2 * y by ring]
    ring
  have hright : (fun x : ℝ ↦
      x * exp (log (1 / sqrt 2) + sqrt 2 * x -
        2 * sqrt 2 * (x - 0))) =
      fun x : ℝ ↦ x * exp (log (1 / sqrt 2) - sqrt 2 * x) := by
    funext x
    rw [show log (1 / sqrt 2) + sqrt 2 * x -
        2 * sqrt 2 * (x - 0) =
        log (1 / sqrt 2) - sqrt 2 * x by ring]
  rw [hleft, hright, MeasureTheory.integral_neg]
  ring

lemma laplace_isIsotropic : IsIsotropic laplaceParam := by
  funext k
  fin_cases k
  · simpa [IsIsotropic, momentMap, isotropicTarget] using laplace_mass
  · simpa [IsIsotropic, momentMap, isotropicTarget] using laplace_mean
  · simpa [IsIsotropic, momentMap, isotropicTarget] using laplace_second

theorem laplace_mem_family6 : laplaceParam ∈ family6 :=
  ⟨laplace_admissible, laplace_isIsotropic⟩

theorem laplace_objective {alpha : ℝ} (halpha : 0 < alpha) :
    objective alpha laplaceParam = L alpha := by
  change integral (LogConcaveClaimI.gAlpha alpha) laplaceParam = L alpha
  rw [laplace_integral_eq (LogConcaveClaimI.gAlpha alpha)
    (Law.pieceIntegrable_gAlpha halpha.le laplace_admissible)]
  change (∫ x : ℝ,
    EndpointWitnesses.gAlpha alpha x * EndpointWitnesses.laplaceDensity x) = L alpha
  simpa only [L, laplaceValue] using
    (EndpointWitnessBridge.laplace_objective_eq_laplaceValue halpha)

/-- The isotropic symmetric Laplace law is an actual member of the tagged
family and realizes the value `L alpha`. -/
theorem exists_laplace_witness (alpha : ℝ) (halpha : 0 < alpha) :
    ∃ p ∈ family6, objective alpha p = L alpha :=
  ⟨laplaceParam, laplace_mem_family6, laplace_objective halpha⟩

end LogConcaveFamily6.EndpointParams

end FlattenedExistenceSection21


/-!
Flattened source section: FinalFamily6Theorem.lean
-/

section FlattenedExistenceSection22

/-!
# The sharp theorem for family (6)

This file keeps the existence argument separate from the exclusion and
endpoint calculations.  The only input to the former is the elementary
quantile-substitution identity for the explicit decoder.
-/



open Set

namespace LogConcaveFamily6

open ProfileCompactification
open ProfileDecode
open ProfileEncode

/-- Claim (iii), with its computational endpoint values rewritten as the
values `S` and `L` used in the statement of the theorem. -/
theorem terminal_objective_le_SL
    {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    {q : Param} (hq : q ∈ family6) (hterminal : TerminalShape q) :
    objective alpha q ≤ max (S alpha) (L alpha) := by
  have h := terminal_objective_le_max halpha halpha1 hq hterminal
  rw [EndpointParams.shiftedValue_eq_S alpha halpha.le] at h
  simpa only [L, laplaceValue] using h

/-- **Existence of a genuine global maximizer.**  This version displays the
single change-of-variables identity on which the compactification proof
depends.  Once that identity is proved for the explicit quantile decoder,
the conclusion has no compactness or attainment hypothesis. -/
theorem family6_objective_attains_of_normalized_quantile_substitution
    {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hquantile : ∀ v : OpenKinkProfile,
      openProfileParam v ∈ normalizedProfiles →
      openProfileObjective alpha v =
        profileObjective alpha (openProfileParam v)) :
    ∃ q ∈ family6, IsMaxOn (objective alpha) family6 q := by
  exact exists_family6_globalMax_of_normalized_quantile_bridge
    halpha hquantile

/-- The pointwise upper bound, conditional only on the explicit
quantile-substitution identity. -/
theorem family6_objective_le_of_normalized_quantile_substitution
    {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hquantile : ∀ v : OpenKinkProfile,
      openProfileParam v ∈ normalizedProfiles →
      openProfileObjective alpha v =
        profileObjective alpha (openProfileParam v)) :
    ∀ q ∈ family6, objective alpha q ≤ max (S alpha) (L alpha) := by
  have hattain :=
    family6_objective_attains_of_normalized_quantile_substitution
      halpha.le hquantile
  exact objective_le_max_of_attainment_and_claimIII halpha hattain
    (fun q hq ht ↦ terminal_objective_le_SL halpha halpha1 hq ht)

/-- The sharp family-(6) theorem, conditional only on the explicit
quantile-substitution identity.  Both endpoint values are realized by actual
members of the tagged family. -/
theorem family6_isGreatest_of_normalized_quantile_substitution
    {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1)
    (hquantile : ∀ v : OpenKinkProfile,
      openProfileParam v ∈ normalizedProfiles →
      openProfileObjective alpha v =
        profileObjective alpha (openProfileParam v)) :
    IsGreatest (objective alpha '' family6)
      (max (S alpha) (L alpha)) := by
  have hattain :=
    family6_objective_attains_of_normalized_quantile_substitution
      halpha.le hquantile
  exact family6_isGreatest_of_attainment_and_claimIII halpha hattain
    (fun q hq ht ↦ terminal_objective_le_SL halpha halpha1 hq ht)
    (EndpointParams.exists_shifted_witness alpha halpha.le)
    (EndpointParams.exists_laplace_witness alpha halpha)

/-- **Existence of a genuine global maximizer for the family-(6)
objective.**  This is the assumption-free form used in Claims (i) and (ii).
Unbounded supports are included. -/
theorem family6_objective_attains
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    ∃ q ∈ family6, IsMaxOn (objective alpha) family6 q := by
  exact ProfileCompactification.exists_family6_globalMax halpha

/-- The unconditional pointwise upper bound on family (6). -/
theorem family6_objective_le
    {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∀ q ∈ family6, objective alpha q ≤ max (S alpha) (L alpha) := by
  have hattain := family6_objective_attains halpha.le
  exact objective_le_max_of_attainment_and_claimIII halpha hattain
    (fun q hq ht ↦ terminal_objective_le_SL halpha halpha1 hq ht)

/-- **Theorem 2 (family (6), formalized).**  For `0 < alpha ≤ 1`, the
maximum of the objective over all isotropic two-piece log-affine laws is
`max (S alpha) (L alpha)`, and this value is attained. -/
theorem theorem2_family6
    {alpha : ℝ} (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) :
    IsGreatest (objective alpha '' family6)
      (max (S alpha) (L alpha)) := by
  have hattain := family6_objective_attains halpha.le
  exact family6_isGreatest_of_attainment_and_claimIII halpha hattain
    (fun q hq ht ↦ terminal_objective_le_SL halpha halpha1 hq ht)
    (EndpointParams.exists_shifted_witness alpha halpha.le)
    (EndpointParams.exists_laplace_witness alpha halpha)

end LogConcaveFamily6

end FlattenedExistenceSection22

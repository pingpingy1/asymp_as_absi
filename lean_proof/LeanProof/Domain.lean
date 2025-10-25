/-
Domain definitions for asymptotic analysis
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Basic

open Real
open ENNReal

def Dd := ℕ → ℝ
def Dc := Set Dd
inductive Da
  | bot : Da
  | elem : ℝ≥0∞ × ℝ → Da
  | top : Da

namespace Dd

def le (f g : Dd) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f n| ≤ (1 + ε) * |g n|
scoped infix:50 " ⊑d " => le

lemma le_refl (f : Dd) : f ⊑d f := by
  intro ε hε
  use 0
  intro n _
  calc |f n| = 1 * |f n| := by ring
    _ ≤ (1 + ε) * |f n| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      linarith

/-
Helper lemma used in the transitivity proof. We prove that (1 + δ)² ≤ 1 + 3δ
when 0 ≤ δ ≤ 1. This bound allows us to compose two ε-approximations.
-/
lemma sq_le_one_add_three_mul {δ : ℝ} (hδ_nonneg : 0 ≤ δ) (hδ_le1 : δ ≤ 1) :
  (1 + δ) ^ 2 ≤ 1 + 3 * δ := by
  -- Expand (1 + δ)² = 1 + 2δ + δ², then use δ² ≤ δ (from 0 ≤ δ ≤ 1)
  have h_sq_le : δ ^ 2 ≤ δ := by
    calc δ ^ 2 = δ * δ := sq δ
      _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hδ_le1 hδ_nonneg
      _ = δ := one_mul δ
  calc (1 + δ) ^ 2 = 1 + 2 * δ + δ ^ 2 := by ring
    _ ≤ 1 + 2 * δ + δ := add_le_add_left h_sq_le _
    _ = 1 + 3 * δ := by ring

/-
Transitivity of ⊑d. The key idea: given f ⊑d g and g ⊑d h for arbitrary ε > 0,
we choose ε' = min(1, ε/3) small enough that (1 + ε')² ≤ 1 + ε. This allows
us to chain the inequalities |f n| ≤ (1 + ε')|g n| ≤ (1 + ε')²|h n| ≤ (1 + ε)|h n|.
-/
lemma le_trans {f g h : Dd} (hfg : f ⊑d g) (hgh : g ⊑d h) : f ⊑d h := by
  intro ε hε
  -- Choose ε' = min(1, ε/3) so that (1 + ε')² ≤ 1 + 3ε' ≤ 1 + ε
  let ε' := min 1 (ε / 3)
  have hε'_pos : ε' > 0 := by
    simp only [ε', lt_min_iff]
    exact ⟨by norm_num, by linarith⟩

  -- Obtain witnesses from both hypotheses
  obtain ⟨N1, hN1⟩ := hfg ε' hε'_pos
  obtain ⟨N2, hN2⟩ := hgh ε' hε'_pos

  use max N1 N2
  intro n hn

  -- Key bounds on ε'
  have hε'_nonneg : 0 ≤ ε' := le_of_lt hε'_pos
  have hε'_le1 : ε' ≤ 1 := min_le_left 1 (ε / 3)
  have hε'_bound : 3 * ε' ≤ ε := by
    have hmin : ε' ≤ ε / 3 := min_le_right 1 (ε / 3)
    calc
      3 * ε' ≤ 3 * (ε / 3) := by apply mul_le_mul_of_nonneg_left hmin; norm_num
      _ = ε := by ring

  -- Chain the inequalities using the helper lemma
  calc |f n| ≤ (1 + ε') * |g n| := hN1 n (le_of_max_le_left hn)
    _ ≤ (1 + ε') * ((1 + ε') * |h n|) :=
      mul_le_mul_of_nonneg_left (hN2 n (le_of_max_le_right hn)) (by linarith)
    _ = (1 + ε') ^ 2 * |h n| := by ring
    _ ≤ (1 + 3 * ε') * |h n| := by
      apply mul_le_mul_of_nonneg_right (sq_le_one_add_three_mul hε'_nonneg hε'_le1) (abs_nonneg _)
    _ ≤ (1 + ε) * |h n| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      linarith

end Dd

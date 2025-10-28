import Mathlib.Tactic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.ENNReal.Basic

/-!
# Domain definitions for asymptotic analysis

This file defines the three semantic domains used in asymptotic analysis:
  * Denotational domain `Dd : ℕ+ → ℝ`
  * Concrete domain `Dc : Set Dd`
  * Abstract domain `Da : ℝ≥0∞ × ℝ` with ⊥ and ⊤

They are equipped with the respective orderings:
  * `Dd`: f ⊑d g iff ∀ ε > 0, ∃ N, ∀ n ≥ N, |f n| ≤ (1 + ε) * |g n|
    - Preorder (reflexive and transitive)
  * `Dc`: A ⊑c B iff A ⊆ B
    - Partial order (reflexive, transitive, and antisymmetric)
  * `Da`: lexicographic order with second component prioritized
    - Partial order (reflexive, transitive, and antisymmetric)

## Main definitions
* `Dd`: Functions from positive naturals to reals
* `Dc`: Sets of functions (powerset of Dd)
* `Da`: Abstract domain with bottom and top elements

## Main results
* `Dd.le_refl`, `Dd.le_trans`: `⊑d` is a preorder
* `Dc.le_refl`, `Dc.le_trans`, `Dc.le_antisymm`: `⊑c` is a partial order
* `Da.le_refl`, `Da.le_trans`, `Da.le_antisymm`: `⊑a` is a partial order
-/

open Real ENNReal

/-- Denotational domain: functions from positive naturals to reals. -/
def Dd := ℕ+ → ℝ

/-- Concrete domain: sets of denotational functions. -/
abbrev Dc := Set Dd

/-- Abstract domain: extended non-negative reals paired with reals,
    plus top and bottom elements. -/
inductive Da
  | bot : Da
  | elem : ℝ≥0∞ × ℝ → Da
  | top : Da

/-- Signed abstract domain: extended reals paired with reals,
    plus top and bottom elements. -/
inductive Dastar
  | bot : Dastar
  | elem : EReal × ℝ → Dastar
  | top : Dastar

namespace Dd

/-- Denotational ordering: f ⊑d g means f is asymptotically dominated by g.
    Formally, for every ε > 0, there exists N such that for all n ≥ N,
    |f n| ≤ (1 + ε) * |g n|. -/
def le (f g : Dd) : Prop :=
  ∀ ε > 0, ∃ N : ℕ+, ∀ n ≥ N, |f n| ≤ (1 + ε) * |g n|

/-- Notation for denotational ordering. -/
scoped infix:50 " ⊑d " => le

/-- Every function is asymptotically dominated by itself. -/
lemma le_refl (f : Dd) : f ⊑d f := by
  intro ε hε
  use 1
  intro n _
  calc |f n| = 1 * |f n| := by ring
           _ ≤ (1 + ε) * |f n| := by
               apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
               linarith

/-- For δ ∈ [0,1], we have (1 + δ)² ≤ 1 + 3δ.
    This inequality is used to control error accumulation in transitivity. -/
private lemma sq_le_one_add_three_mul {δ : ℝ} (hδ_nonneg : 0 ≤ δ) (hδ_le1 : δ ≤ 1) :
    (1 + δ) ^ 2 ≤ 1 + 3 * δ := by
  have h_sq_le : δ ^ 2 ≤ δ := by
    calc δ ^ 2 = δ * δ := by rw[sq]
             _ ≤ 1 * δ := mul_le_mul_of_nonneg_right hδ_le1 hδ_nonneg
             _ = δ := one_mul δ
  calc (1 + δ) ^ 2 = 1 + 2 * δ + δ ^ 2 := by ring
                 _ ≤ 1 + 2 * δ + δ := add_le_add_left h_sq_le _
                 _ = 1 + 3 * δ := by ring

/-- Asymptotic dominance is transitive: if f ⊑d g and g ⊑d h, then f ⊑d h. -/
lemma le_trans {f g h : Dd} (hfg : f ⊑d g) (hgh : g ⊑d h) : f ⊑d h := by
  intro ε hε
  -- Choose δ = min(1, ε/3) to ensure (1 + δ)² ≤ 1 + 3δ ≤ 1 + ε
  set δ := min 1 (ε / 3) with hδ_def
  have hδ_pos : 0 < δ := lt_min (by norm_num) (by linarith)

  -- Get witnesses from both hypotheses
  obtain ⟨N1, hN1⟩ := hfg δ hδ_pos
  obtain ⟨N2, hN2⟩ := hgh δ hδ_pos
  refine ⟨max N1 N2, fun n hn => ?_⟩

  -- Establish key bounds on δ
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hδ_le1 : δ ≤ 1 := min_le_left ..
  have h3δ : 3 * δ ≤ ε := by
    calc 3 * δ ≤ 3 * (ε / 3) := by apply mul_le_mul_of_nonneg_left (min_le_right ..) (by norm_num)
             _ = ε := by ring

  -- Chain the inequalities
  calc |f n| ≤ (1 + δ) * |g n| := by apply hN1 n (le_of_max_le_left hn)
           _ ≤ (1 + δ) * ((1 + δ) * |h n|) :=
               mul_le_mul_of_nonneg_left (hN2 n (le_of_max_le_right hn)) (by linarith)
           _ = (1 + δ) ^ 2 * |h n| := by ring
           _ ≤ (1 + 3 * δ) * |h n| :=
               mul_le_mul_of_nonneg_right (sq_le_one_add_three_mul hδ_nonneg hδ_le1) (abs_nonneg _)
           _ ≤ (1 + ε) * |h n| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)

end Dd

namespace Dc

/-- Concrete ordering: subset inclusion. -/
def le (A B : Dc) : Prop := ∀ f : Dd, A f → B f

/-- Notation for concrete ordering. -/
scoped infix:50 " ⊑c " => le

/-- Subset inclusion is reflexive. -/
lemma le_refl (A : Dc) : A ⊑c A := fun _ hf => hf

/-- Subset inclusion is antisymmetric. -/
lemma le_antisymm {A B : Dc} (hAB : A ⊑c B) (hBA : B ⊑c A) : A = B :=
  Set.ext fun f => ⟨hAB f, hBA f⟩

/-- Subset inclusion is transitive. -/
lemma le_trans {A B C : Dc} (hAB : A ⊑c B) (hBC : B ⊑c C) : A ⊑c C :=
  fun f hfA => hBC f (hAB f hfA)

end Dc

instance : PartialOrder Dc where
  le := Dc.le
  le_refl := Dc.le_refl
  le_trans := @Dc.le_trans
  le_antisymm := @Dc.le_antisymm
namespace Da

/-- Lexicographic ordering on the abstract domain, with the real component prioritized. -/
def le (a b : Da) : Prop :=
  match a, b with
  | bot, _ => True
  | _, top => True
  | top, _ => False
  | _, bot => False
  | elem (c1, r1), elem (c2, r2) =>
      r1 < r2 ∨ (r1 = r2 ∧ c1 ≤ c2)

/-- Notation for abstract ordering. -/
scoped infix:50 " ⊑a " => le

/-- Every abstract element is related to itself. -/
lemma le_refl (a : Da) : a ⊑a a := by
  cases a
  · trivial  -- bot case
  · right; exact ⟨rfl, le_rfl⟩  -- elem case
  · trivial  -- top case

/-- The abstract ordering is antisymmetric. -/
lemma le_antisymm {a b : Da} (hab : a ⊑a b) (hba : b ⊑a a) : a = b := by
  cases a <;> cases b
  · rfl  -- bot, bot
  · trivial  -- bot, elem - impossible by hab = True and hba = False
  · trivial  -- bot, top
  · contradiction  -- elem, bot
  · -- elem, elem
    rename_i p1 p2
    rcases hab with hlt | ⟨heq, hle⟩
    · rcases hba with hlt' | ⟨heq', hle'⟩
      · linarith  -- r1 < r2 and r2 < r1 contradiction
      · linarith  -- r1 < r2 and r2 = r1 contradiction
    · rcases hba with hlt' | ⟨heq', hle'⟩
      · linarith  -- r1 = r2 and r2 < r1 contradiction
      · -- r1 = r2 and c1 ≤ c2 and r2 = r1 and c2 ≤ c1
        congr 1
        exact Prod.ext (le_antisymm_iff.mpr ⟨hle, hle'⟩) heq
  · trivial  -- elem, top
  · trivial  -- top, bot
  · trivial  -- top, elem
  · rfl  -- top, top

/-- The abstract ordering is transitive. -/
lemma le_trans {a b c : Da} (hab : a ⊑a b) (hbc : b ⊑a c) : a ⊑a c := by
  cases a <;> cases b <;> cases c <;> try trivial
  · -- elem, elem, elem
    rename_i p1 p2 p3
    obtain ⟨c1, r1⟩ := p1
    obtain ⟨c2, r2⟩ := p2
    obtain ⟨c3, r3⟩ := p3
    rcases hab with hlt_ab | ⟨heq_ab, hle_ab⟩ <;>
    rcases hbc with hlt_bc | ⟨heq_bc, hle_bc⟩
    · left; linarith  -- r1 < r2 < r3
    · left; linarith  -- r1 < r2 = r3
    · left; linarith  -- r1 = r2 < r3
    · right  -- r1 = r2 = r3
      constructor
      · exact heq_ab.trans heq_bc
      · exact hle_ab.trans hle_bc

end Da

instance : PartialOrder Da where
  le := Da.le
  le_refl := Da.le_refl
  le_trans := @Da.le_trans
  le_antisymm := @Da.le_antisymm

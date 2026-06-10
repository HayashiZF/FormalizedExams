import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Interval.Set.Defs


/-
-------- Problem 19 -----------
-/

def δ (x : ℝ) (f : ℝ → ℝ) : Set ℝ := {d : ℝ | f (x + d) > f x}

abbrev MonotoneIncreasingPos (f : ℝ → ℝ) := ∀ x₁ x₂ : ℝ, 0 < x₁ ∧ 0 < x₂ ∧  x₁ < x₂ → f x₁ < f x₂

open Set

/- (1) -/
example (f : ℝ → ℝ) (x : ℝ) : x ≥ 0 ∧ f x = 1 - x → δ x f = Ioo 0 (3 / 2) := by
  intro h
  unfold δ Ioo
  sorry

/- (2) -/
example (hOdd : ∀ x : ℝ, f (-x) = -f x) : ∀ x₁ x₂ : ℝ, f x₁ ≤ f x₂ ∧ x₁ ≠ 0 ∧ x₂ ≠ 0 →
    δ x₂ f ⊆ δ x₁ f := by
  sorry

/- (3) i -/
example {x : ℝ} {f : ℝ → ℝ} (h1 : ∀ x < 0, f x = Real.exp x)
    (h2 : ∀ x₁ x₂ : ℝ, f x₁ ≤ f x₂ → (δ x₂ f) ⊆ (δ x₁ f)) : f 0 ≥ 1 := by
  by_contra!




/- (3) ii -/
example {x : ℝ} {f : ℝ → ℝ} (h1 : ∀ x < 0, f x = Real.exp x)
    (h2 : ∀ x₁ x₂ : ℝ, f x₁ ≤ f x₂ → (δ x₂ f) ⊆ (δ x₁ f)) :
    MonotoneIncreasingPos f := by

    sorry

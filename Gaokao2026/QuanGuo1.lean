import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Monotone.Defs
import Mathlib.Order.Interval.Set.Defs

/- global answer placeholder -/
variable {PlaceHolder : Type}

/-
-------- Problem 15 ----------
Problem Statement:
In a right triangular prism ABC-A₁B₁C₁, ∠ACB = 90°, AC = BC.
D and E are the midpoints of AB and A₁C₁ respectively.
(1) Prove: DE // plane BCC₁B₁.
(2) Let CC₁ = 2. If the angle between line DE and plane ACC₁A₁ is 45°,
    find the distance from line DE to plane BCC₁B₁.
-/

-- Basic 3D definitions
noncomputable def dot_product3 (u v : ℝ × ℝ × ℝ) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

noncomputable def vec_length3 (u : ℝ × ℝ × ℝ) : ℝ :=
  Real.sqrt (dot_product3 u u)

noncomputable def distance3 (P Q : ℝ × ℝ × ℝ) : ℝ :=
  vec_length3 (Q.1 - P.1, Q.2.1 - P.2.1, Q.2.2 - P.2.2)

/-- Midpoint of two points in 3D -/
def is_midpoint3 (M P Q : ℝ × ℝ × ℝ) : Prop :=
  M.1 = (P.1 + Q.1) / 2 ∧ M.2.1 = (P.2.1 + Q.2.1) / 2 ∧ M.2.2 = (P.2.2 + Q.2.2) / 2

/--
  Geometric setup for the right triangular prism ABC-A₁B₁C₁
  with ∠ACB = 90°, AC = BC = a, and CC₁ = h.
  We use a standard coordinate system with C at the origin.
-/
def PrismSetup (a h : ℝ) (A B C A1 B1 C1 : ℝ × ℝ × ℝ) : Prop :=
  a > 0 ∧ h > 0 ∧
  C = (0, 0, 0) ∧
  A = (a, 0, 0) ∧
  B = (0, a, 0) ∧
  C1 = (0, 0, h) ∧
  A1 = (a, 0, h) ∧
  B1 = (0, a, h)

/-- The normal vector to plane BCC₁B₁ is (1, 0, 0) -/
def normal_BCC1B1 : ℝ × ℝ × ℝ := (1, 0, 0)

/-- The normal vector to plane ACC₁A₁ is (0, 1, 0) -/
def normal_ACC1A1 : ℝ × ℝ × ℝ := (0, 1, 0)

/--
  Sine of the angle between a line with direction vector v and a plane with normal n.
-/
noncomputable def sin_angle_line_plane (v n : ℝ × ℝ × ℝ) : ℝ :=
  |dot_product3 v n| / (vec_length3 v * vec_length3 n)

/--
  Distance from a point P to the plane passing through origin with given normal vector.
-/
noncomputable def distance_point_plane_origin (P n : ℝ × ℝ × ℝ) : ℝ :=
  |dot_product3 P n| / vec_length3 n

theorem gaokao2026_q1_p15_part1
    (a h : ℝ) (A B C A1 B1 C1 D E : ℝ × ℝ × ℝ)
    (h_setup : PrismSetup a h A B C A1 B1 C1)
    (h_D : is_midpoint3 D A B)
    (h_E : is_midpoint3 E A1 C1) :
    dot_product3 (E.1 - D.1, E.2.1 - D.2.1, E.2.2 - D.2.2) normal_BCC1B1 = 0 := by
  sorry

theorem gaokao2026_q1_p15_part2
    (a : ℝ) (A B C A1 B1 C1 D E : ℝ × ℝ × ℝ)
    (h_setup : PrismSetup a 2 A B C A1 B1 C1)
    (h_D : is_midpoint3 D A B)
    (h_E : is_midpoint3 E A1 C1)
    (h_angle : sin_angle_line_plane (E.1 - D.1, E.2.1 - D.2.1, E.2.2 - D.2.2) normal_ACC1A1 = Real.sqrt 2 / 2) :
    distance_point_plane_origin D normal_BCC1B1 = 2 := by
  sorry

/- -------- Problem 16 ----------
In triangle ABC, AB = 3, BC = 2√3, and cos B = √3/3.
(1) Find cos A.
(2) Let points D and E satisfy: D is on the extension of BA past A, DE // BC, and AE ⊥ AC.
    If DE = √6, find CE.
-/

noncomputable def dot_product (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

noncomputable def vec_length (u : ℝ × ℝ) : ℝ := Real.sqrt (u.1^2 + u.2^2)

noncomputable def distance (A B : ℝ × ℝ) : ℝ := vec_length (B.1 - A.1, B.2 - A.2)

noncomputable def cos_angle (A B C : ℝ × ℝ) : ℝ :=
  let v1 := (A.1 - B.1, A.2 - B.2)
  let v2 := (C.1 - B.1, C.2 - B.2)
  dot_product v1 v2 / (vec_length v1 * vec_length v2)

/-- D is on the extension of BA past A -/
def on_extension_BA (B A D : ℝ × ℝ) : Prop :=
  ∃ t : ℝ, t > 0 ∧ (D.1 - A.1 = t * (A.1 - B.1)) ∧ (D.2 - A.2 = t * (A.2 - B.2))

/-- DE is parallel to BC -/
def parallel (D E B C : ℝ × ℝ) : Prop :=
  ∃ s : ℝ, (E.1 - D.1 = s * (C.1 - B.1)) ∧ (E.2 - D.2 = s * (C.2 - B.2))

/-- AE is perpendicular to AC -/
def perpendicular (A E C : ℝ × ℝ) : Prop :=
  dot_product (E.1 - A.1, E.2 - A.2) (C.1 - A.1, C.2 - A.2) = 0

/- (1) -/
example (A B C : ℝ × ℝ) (h_AB : distance A B = 3) (h_BC : distance B C = 2 * Real.sqrt 3)
    (h_cosB : cos_angle A B C = Real.sqrt 3 / 3) : cos_angle B A C = 1 / 3 := by
  sorry

example (A B C D E : ℝ × ℝ) (h_AB : distance A B = 3) (h_BC : distance B C = 2 * Real.sqrt 3)
    (h_cosB : cos_angle A B C = Real.sqrt 3 / 3) (h_D : on_extension_BA B A D) (h_para : parallel D E B C)
    (h_perp : perpendicular A E C) (h_DE : distance D E = Real.sqrt 6) :
    distance C E = 3 * Real.sqrt 5 := by
  sorry

/-
-------- Problem 17 ----------
Problem Statement:
Let integer N ≥ 2. A student practices shooting a basketball, throwing at most N times.
The student stops practicing if and only if they make exactly 1 shot or if they miss all N shots.
Let the probability of making a shot each time be p (0 < p < 1), and each shot is independent.
Let X be the number of throws when the student stops practicing.
-/

-- Define the problem's constraints
variable {N : ℕ} (hN : N ≥ 2)
variable {p : ℝ} (hp_lower : 0 < p) (hp_upper : p < 1)

/--
The probability mass function of X.
If n < N, P(X = n) is the probability of missing n-1 times and making the n-th shot.
If n = N, P(X = N) is the probability of missing N-1 times (the final shot doesn't matter for stopping).
-/
noncomputable def probX (N : ℕ) (p : ℝ) (n : ℕ) : ℝ :=
  if n = 0 ∨ n > N then
    0
  else if n < N then
    (1 - p)^(n - 1) * p
  else -- n = N
    (1 - p)^(N - 1)

/--
The cumulative tail probability P(X > k).
Since X takes values up to N, P(X > k) is the sum of the PMF from k+1 to N.
Finset.Ioc k N represents the integer interval (k, N].
-/
noncomputable def probX_gt (N : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ioc k N, probX N p i

/--
Conditional probability P(A | B) = P(A ∩ B) / P(B).
For events (X > a) and (X > b), the intersection is X > max(a, b).
-/
noncomputable def conditional_probX_gt (N : ℕ) (p : ℝ) (a b : ℕ) : ℝ :=
  probX_gt N p (max a b) / probX_gt N p b

--  (1): When N = 4, p = 1/3, find the distribution of X.
example : probX 4 (1/3) 1 = 1/3 ∧ probX 4 (1/3) 2 = 2/9 ∧
    probX 4 (1/3) 3 = 4/27 ∧ probX 4 (1/3) 4 = 8/27 := by
  sorry

--  (2): Let k, m be natural numbers.

-- (i) When k ≤ N - 1, find P(X > k).
example (k : ℕ) (hk : k ≤ N - 1) : probX_gt N p k = (1 - p)^k := by
  sorry

-- (ii) When k + m ≤ N - 1, prove P(X > k + m | X > k) = P(X > m).
--  memoryless property
example (k m : ℕ) (hkm : k + m ≤ N - 1) :
    conditional_probX_gt N p (k + m) k = probX_gt N p m := by
  sorry

/-
-------- Problem 18 ----------
Problem Statement:
Given an ellipse C: x²/a² + y²/b² = 1 (a > b > 0) with left focus F(-1, 0) and eccentricity e = 1/2.
(1) Find the equation of C.
    (Solution: c = 1, a = 2, b² = 3. Equation is x²/4 + y²/3 = 1)
(2) Let O(0,0) be the origin. A line l passing through F with slope k > 0 intersects C at P and Q.
    Q is in the third quadrant. Line PO intersects C at another point R.
    (i) If Area(ΔPQR) = 3 * Area(ΔPFO), find the equation of l.
    (ii) Find the minimum value of tan(∠PQR).
-/

-- Basic Geometric Definitions

/-- The specific ellipse C found in part 1: x²/4 + y²/3 = 1 -/
def on_ellipse (p : ℝ × ℝ) : Prop := p.1^2 / 4 + p.2^2 / 3 = 1

/-- Point F is the left focus (-1, 0) -/
def F : ℝ × ℝ := (-1, 0)

/-- Origin O (0, 0) -/
def O : ℝ × ℝ := (0, 0)

/-- A line passing through F(-1, 0) with slope k -/
def on_line_l (k : ℝ) (p : ℝ × ℝ) : Prop := p.2 = k * (p.1 + 1)

/-- Q is in the third quadrant -/
def third_quadrant (p : ℝ × ℝ) : Prop := p.1 < 0 ∧ p.2 < 0

/-- The area of a triangle given three points using the determinant formula. -/
noncomputable def triangle_area (A B C : ℝ × ℝ) : ℝ :=
  0.5 * |A.1 * (B.2 - C.2) + B.1 * (C.2 - A.2) + C.1 * (A.2 - B.2)|

/-- Tangent of the angle between two vectors QA and QB radiating from a vertex.
    Calculated using |cross product| / (dot product). -/
noncomputable def tan_angle (vertex A B : ℝ × ℝ) : ℝ :=
  let v1 := (A.1 - vertex.1, A.2 - vertex.2)
  let v2 := (B.1 - vertex.1, B.2 - vertex.2)
  let cross_prod := v1.1 * v2.2 - v1.2 * v2.1
  let dot_prod := v1.1 * v2.1 + v1.2 * v2.2
  |cross_prod| / dot_prod

variable (k : ℝ) (hk : k > 0)
variable (P Q R : ℝ × ℝ)

-- P and Q are the intersections of the line l and the ellipse C
variable (hP_ell : on_ellipse P) (hP_lin : on_line_l k P)
variable (hQ_ell : on_ellipse Q) (hQ_lin : on_line_l k Q)
variable (hPQ_neq : P ≠ Q)

-- Q is explicitly in the third quadrant
variable (hQ_quad : third_quadrant Q)

-- R is the other intersection of line PO and C.
-- Since the ellipse is symmetric about the origin, R is exactly the reflection of P.
variable (hR_symm : R = (-P.1, -P.2))

/--
Part 2 (i): If the area of ΔPQR is 3 times the area of ΔPFO, find the slope k.
The expected mathematical answer is k = √6 / 2.
-/
example (h_area : triangle_area P Q R = 3 * triangle_area P F O) : k = Real.sqrt 6 / 2 := by
  sorry

/--
Part 2 (ii): Find the minimum value of tan(∠PQR).
The expected mathematical minimum is √2.
-/
example :
    ∃ (min_val : ℝ), min_val = Real.sqrt 2 ∧
    ∀ (k' : ℝ) (hk' : k' > 0) (P' Q' R' : ℝ × ℝ),
      on_ellipse P' → on_line_l k' P' →
      on_ellipse Q' → on_line_l k' Q' → P' ≠ Q' → third_quadrant Q' →
      R' = (-P'.1, -P'.2) →
      tan_angle Q' P' R' ≥ min_val := by
  sorry


/-
-------- Problem 19 -----------
-/

def δ (x : ℝ) (f : ℝ → ℝ) : Set ℝ := {d : ℝ | f (x + d) > f x}

abbrev MonotoneIncreasingPos (f : ℝ → ℝ) := ∀ x₁ x₂ : ℝ, 0 < x₁ ∧ 0 < x₂ ∧  x₁ < x₂ → f x₁ < f x₂

open Set

/- (1) -/
/- answer: Ioo 0 (3 / 2) -/
example (f : ℝ → ℝ) (x : ℝ) : x ≥ 0 ∧ f x = 1 - x → δ x f = PlaceHolder := by
  intro h
  sorry

/- (2) -/
example (hOdd : ∀ x : ℝ, f (-x) = -f x) : ∀ x₁ x₂ : ℝ, f x₁ ≤ f x₂ ∧ x₁ ≠ 0 ∧ x₂ ≠ 0 →
    δ x₂ f ⊆ δ x₁ f := by
  sorry

/- (3) i -/
example {x : ℝ} {f : ℝ → ℝ} (h1 : ∀ x < 0, f x = Real.exp x)
    (h2 : ∀ x₁ x₂ : ℝ, f x₁ ≤ f x₂ → (δ x₂ f) ⊆ (δ x₁ f)) : f 0 ≥ 1 := by
  by_contra!
  sorry

/- (3) ii -/
example {x : ℝ} {f : ℝ → ℝ} (h1 : ∀ x < 0, f x = Real.exp x)
    (h2 : ∀ x₁ x₂ : ℝ, f x₁ ≤ f x₂ → (δ x₂ f) ⊆ (δ x₁ f)) :
    MonotoneIncreasingPos f := by

    sorry

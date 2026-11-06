import Mathlib

/-- Auxiliary lemma : for any real numbers $x$ and $y$, $(x+y)^2 \leq 2*(x^2 + y^2)$. -/
lemma p93' {x y : ℝ} : (x + y)^2 ≤ 2*(x^2 + y^2) := by
  let f := fun i : ℕ => match i with
    | 0 => x
    | _ => y
  let s := Finset.range 2
  have : ∑ i ∈ s, f i  = x + y := by
    dsimp [f,s]
    rw [← (show {0, 1} = Finset.range 2 by rfl),Finset.sum_pair (by norm_num)]
  rw [← this]
  have : s.card = (2 : ℝ) := by rfl
  rw [← this]
  have : ∑ i ∈ s, (f i) ^ 2 = x^2 + y^2 := by
    dsimp [f,s]
    rw [← (show {0, 1} = Finset.range 2 by rfl),Finset.sum_pair (by norm_num)]
  rw [← this]
  apply sq_sum_le_card_mul_sum_sq

/-- Let $x,$ $y,$ $z$ be real numbers such that $x + y + z = 5$ and $xy + xz + yz = 8.$  Find the largest possible value of $x.$-/
theorem intermediate_algebra_4105 : (∀ (x y z : ℝ), x + y + z = 5 ∧ x*y + x*z + y*z = 8 → x ≤ 7 / 3) ∧
            ∃ x, ∃ y, ∃ z, x + y + z = (5 : ℝ) ∧ x*y + x*z + y*z = (8 : ℝ) ∧ x = 7 / 3 := by
  constructor
  · intro x y z ⟨h₁,h₂⟩
    -- use above lemma to have $(y + z)^2 ≤ 2*(y^2 + z^2)$
    have : (y + z)^2 ≤ 2*(y^2 + z^2) := p93'
    nlinarith
  · use 7 / 3; use 4 / 3; use 4 / 3
    ring_nf; aesop

import Mathlib

/-Find all functions $f: \mathbb{N} \rightarrow \mathbb{N}$ (where $\mathbb{N}$ is the set of the natural numbers and is assumed to contain 0 ), such that

$$
f\left(x^{2}\right)-f\left(y^{2}\right)=f(x+y) f(x-y)
$$

for all $x, y \in \mathbb{N}$ with $x \geq y$.-/
theorem number_theory_608022 (f : ℕ → ℕ) : (∀ x y, y ≤ x → (f (x ^ 2) : ℤ) - f (y ^ 2) =
f (x + y) * f (x - y)) ↔ (f = 0 ∨ f = id) := by
  constructor
  -- Assuming the functional equation, we first show that $f(0)=0$
  · intro heq; simp [funext_iff]
    have f0 : f 0 = 0 := by specialize heq 0 0 (by simp); simp at heq; exact heq
  -- Prove that $f(1)$ is $0$ or $1$
    have fsq : ∀ x, f (x ^ 2) = f x ^ 2 := by
      intro x; specialize heq x 0; simp [f0, ← pow_two] at heq; zify; exact heq
    have f1 : f 1 = 0 ∨ f 1 = 1 := by
      specialize fsq 1; simp [pow_two] at fsq; by_cases h : f 1 = 0; left; exact h
      right; symm at fsq; rw [Nat.mul_left_eq_self_iff] at fsq; exact fsq; omega
  -- If $f(1)=0$, prove that $f=0$ by induction
    rcases f1 with f1|f1
    · left; have fsucc : ∀ x, f (x + 1) = f x := by
        intro x; rw [← pow_left_inj₀ _ _ (show 2≠0 by simp), ← fsq, ← fsq]
        zify; rw [← sub_eq_zero, heq, Nat.add_sub_cancel_left, f1]; any_goals simp
      intro x; induction x with
      | zero => exact f0
      | succ n ih => rw [fsucc]; exact ih
  -- If $f(1)=1$, we first prove that $f(2)=2$
    simp_rw [fsq] at heq; have f2 : f 2 = 2 := by
    -- Plug in $x=3$ and $y=1$ to heq and simplify
      have h1 := heq 3 1; simp [f1] at h1
      rw [show 4 = 2^2 by simp, fsq] at h1
    -- Plug in $x=2$ and $y=1$ to heq and simplify
      have h2 := heq 2 1; simp [f1] at h2; rw [← h2, ← sub_eq_zero] at h1
      push_cast at h1; ring_nf at h1
    -- Solve for $f(2)=2$
      simp [show -((f 2)^2*(2:ℤ))-(f 2)^3+↑(f 2)^4 = (f 2)^2*(f 2 + 1)*(f 2-2) by ring] at h1
      norm_cast at h1; simp at h1; rcases h1 with f2|f2
      · simp [f2] at h2
      rw [Int.subNatNat_eq_coe, sub_eq_zero] at f2; zify; exact f2
  -- Prove that $f(x)=x$ by strong parity induction
    right; intro x; induction x using Nat.evenOddStrongRec with
    | h_even x ih =>
      by_cases hx : x < 2
      · interval_cases x; simp [hx, f0]; simp [f2]
      specialize heq (x+1) (x-1) (by omega); rw [add_assoc, Nat.add_sub_cancel', ← two_mul] at heq
      rw [Nat.add_sub_sub_cancel, f2, ih, ih] at heq; push_cast at heq
      rw [Nat.cast_sub] at heq; push_cast at heq; ring_nf at heq; norm_cast at heq
      ring_nf; rw [← mul_left_inj' (show 2≠0 by simp), ← heq]; ring; all_goals omega
    | h_odd x ih =>
      by_cases hx : x < 1
      · simp at hx; simp [hx, f1]
      specialize heq (x+1) x (by simp); rw [Nat.add_sub_cancel_left, f1, ih, ih] at heq
      push_cast at heq; ring_nf at heq; ring_nf; zify; symm; exact heq
      all_goals omega
-- Conversely, it is straightforward to check that $f=0$ and $f=id$ satisfy the functional equation in question
  intro h; rcases h; all_goals simp_all
  intros; ring
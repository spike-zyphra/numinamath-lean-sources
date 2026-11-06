import Mathlib

/-The function $y=\sin (x+φ) (0\leqslant φ\leqslant π)$ is an even function on $\mathbb{R}$. Find the value of $φ$.-/
theorem algebra_9291 {φ : ℝ} (hφ : φ ∈ Set.Icc 0 Real.pi) :
(∀ x, (fun x => Real.sin (x + φ)) (-x)=(fun x => Real.sin (x + φ)) x) ↔ φ = Real.pi / 2 := by
--Rewrite assumptions and break "iff"
  have pi_pos := Real.pi_pos
  simp at hφ; rcases hφ with ⟨h1, h2⟩; simp; constructor
  · intro h
-- Plug in $a=pi/2$ to h and we can an equation on $φ$
    have := h (Real.pi/2)
    rw [add_comm, ← sub_eq_add_neg, add_comm] at this
-- Use trig equalities to simplify the equation and solve for $φ$
    rw [Real.sin_add_pi_div_two, Real.sin_sub_pi_div_two] at this
    rw [neg_eq_self ℝ, Real.cos_eq_zero_iff] at this
    rcases this with ⟨k, hk⟩; rw [hk] at h1 h2
    rw [mul_div_assoc, mul_nonneg_iff] at h1; cases h1
    rename_i h1; rcases h1 with ⟨h1,_⟩
-- Rewrite assumptions to get inequalities on $k$ and solve for $k$
    rw [mul_div_assoc, ← le_div_iff₀, div_div_cancel'] at h2;
    norm_cast at h1 h2; by_cases h' : 1 ≤ k; linarith; push_neg at h'
    by_cases h'' : k ≤ (-1); linarith; push_neg at h''
    have : k = 0 := by linarith
-- Plug in $k=0$ at hk and prove the final goal
    simp [this] at hk; assumption
    linarith; linarith; linarith
-- Prove the reversed implication by plug in $φ=pi/2$
  intro h a; simp [h, Real.sin_add_pi_div_two]
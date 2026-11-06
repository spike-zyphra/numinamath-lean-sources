import Mathlib

open Real

/- Let \( n \) be a positive integer and let \( \alpha = \frac{1+\sqrt{5}}{2} \). Then \( u_n > \alpha^{n-2} \) for \( n \geq 3 \).-/
theorem number_theory_4531 {u : ℕ → ℕ} (hu0 : u 0 = 1) (hu1 : u 1 = 1)
    (hun :∀ n, u (n + 2) = u (n + 1) + u n) {α : ℝ} (hα : α = (1 + √5) / 2) (n : ℕ) :
    α ^ n < u (n + 2) := by
  have hu2 := hun 0
  rw [zero_add, hu0, hu1, show 1+1=2 by norm_num] at hu2
  have hu3 := hun 1
  rw [show 1+2=3 by norm_num, show 1+1=2 by norm_num, hu2, hu1, show 1+2=3 by norm_num] at hu3
--    Since \( \alpha = \frac{1+\sqrt{5}}{2} \) is a root of the equation \( x^2 - x - 1 = 0 \), it follows that \( \alpha^2 = \alpha + 1 \). Therefore, we can express \( \alpha^{n-1} \) as follows:
-- \[
-- \alpha^{n-1} = \alpha^2 \cdot \alpha^{n-3} = (\alpha + 1) \cdot \alpha^{n-3} = \alpha^{n-2} + \alpha^{n-3}.
-- \]
  have hαn (n : ℕ) : α^(n+2) = α^(n+1) + α^n := by
    have : α^2 = α + 1 := by simp [hα]
    apply_fun (α^n * ·) at this
    rwa [← pow_add, mul_add, ← pow_succ, mul_one] at this
  --  Next, we assume that the inequality \( \alpha^{k-2} < u_k \) holds for all integers \( k \) such that \( k \leq n \).
  induction' n using Nat.strongRecOn with n ih
  cases' n with n
  . simp [hu2]
  cases' n with n
  . simp [hu3, hα]
    suffices 1+√5 < 6 by linarith
    suffices √5 < 5 by linarith
    rw [sqrt_lt' (by norm_num)]
    norm_num
--    By our induction hypothesis, we know that:
-- \[
-- \alpha^{n-2} < u_n \quad \text{and} \quad \alpha^{n-3} < u_{n-1}.
-- \]
  have ihn := ih n (by omega)
  have ihnsucc := ih (n+1) (by omega)
  rw [show n+1+2=n+3 by omega] at ihnsucc
  rw [show n+1+1=n+2 by omega, hαn, hun, show n+2+1=n+3 by omega]
  push_cast
--    Adding these inequalities gives us:
-- \[
-- \alpha^{n-1} < u_n + u_{n-1} = u_{n+1}.
-- \]
  exact add_lt_add ihnsucc ihn

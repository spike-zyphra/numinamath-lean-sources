import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/-We need the following lemma on division relations-/
lemma lm_8500 (p : ℕ): Odd p → 16 ∣ p ^ 4 - 1 := by
-- Prove by induction
  intro hp; rcases hp with ⟨k, hk⟩; rw [hk]
  have (t : ℕ): 16 ∣ (2 * t + 1) ^ 4 - 1 := by
    induction t with
  | zero => simp
  | succ n ih =>
    rcases ih with ⟨w, hw⟩; use w+n^3*4+n^2*12+n*13+5
    nth_rw 3 [add_assoc]; nth_rw 2 [add_assoc]; nth_rw 1 [add_assoc]
    nth_rw 2 [mul_add]; rw [← hw]; ring_nf; rw [← Nat.add_sub_assoc]
    ring_nf; rw [add_assoc, add_assoc, add_assoc]; simp
  apply this

/-$p$  is a prime number that is greater than  $2$ . Let  $\{ a_{n}\}$  be a sequence such that  $ na_{n+1}= (n+1) a_{n}-\left( \frac{p}{2}\right)^{4}$ .

Show that if  $a_{1}=5$ , then  $16 \mid a_{81}$ .-/
theorem number_theory_8500 (p : ℕ) (a : ℕ → ℚ)
(hp : Nat.Prime p) (h1 : 2 < p)
(h2 : ∀ n, n * a (n + 1) = (n + 1) * a n - ((p : ℚ) / 2) ^ 4)
(h3 : a 1 = 5) : ∃ t : ℤ, a 81 = t ∧ 16 ∣ t := by
-- Prove that $a(n)$ is equal to $n*a(1)-(p/2)^4 *(n-1)$ by induction
  have r1 : ∀ n : ℕ, n > 0 → a n = n * a 1 - ((p : ℚ) / 2) ^ 4 * (n - 1) := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      by_cases h' : n ≤ 0; simp at h'; rw [h']; simp
      push_neg at h'; simp
      replace ih := ih h'
      have r1 := h2 n
      rw [ih] at r1; ring_nf at r1; ring_nf
      rw [pow_two, mul_assoc, ← mul_add, mul_assoc, mul_assoc] at r1
      rw [← mul_add] at r1; simp at r1; rcases r1 with r1l | r1r
      · rw [r1l]; ring
      linarith
-- Plug in $n=81$ and compute $a(81)$
  have r2 := r1 81
  rw [h3] at r2; simp at r2
  have r3 : a 81 = 400 - 5 * (p ^ 4 - 1) := by
    rw [r2]; ring
-- Apply lemma lm and prove that $16$ divides $400-5*(p^4-1)$
  use 400 - 5 * (p ^ 4 - 1); constructor
  · rw [r3]; simp
  have r4 : Odd p := by apply Prime.odd_of_ne_two; assumption; linarith
  replace r4 := lm_8500 p r4
  apply Int.dvd_sub; norm_num; rcases r4 with ⟨k, hk⟩
  use 5 * k; rw [Nat.sub_eq_iff_eq_add] at hk
  apply Int.natCast_inj.mpr at hk; simp at hk
  rw [hk]; ring; apply Nat.one_le_pow; linarith

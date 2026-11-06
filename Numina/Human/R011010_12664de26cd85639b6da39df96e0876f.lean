import Mathlib

/- we prove that the product of any consecutive integers is divisible by 6 -/
theorem number_theory_5009 (n : ℕ) : 6 ∣ n * (n + 1) * (n + 2) := by
  --show the product of any consecutive integers is divisible by induction
  have r1 : 3 ∣ n * (n + 1) * (n + 2) := by
    induction n with
    | zero => simp
    | succ n ih =>
                  rw [add_assoc, add_assoc];
                  simp; rw [mul_add]
                  rcases ih with ⟨c, hc⟩; use (c + (n + 1) * (n + 2))
                  nth_rw 3 [mul_add]; rw [← hc]; ring
  --show by cases that the product of any consecutive integers is divisible by 2
  have r2 : 2 ∣ n * (n + 1) * (n + 2) := by
    rcases Nat.even_or_odd' n with ⟨k, hk⟩
    cases hk with
    | inl hll => rw [hll, mul_assoc, mul_assoc]; simp
    | inr hrr => rw [hrr]; ring_nf; use (3 + k * 11 + k ^ 2 * 12 + k ^ 3 * 4); ring
  --apply Nat.lcm_dvd and prove the desired result
  have : 6 = Nat.lcm 2 3 := by norm_num
  rw [this]; exact Nat.lcm_dvd r2 r1

import Mathlib

theorem number_theory_74349 (n : ℕ) (hn : n > 0)
    (h : ∀ i ∈ Finset.range 35, Nat.lcm n (n + i) > Nat.lcm n (n + i + 1)) :
    Nat.lcm n (n + 35) > Nat.lcm n (n + 36) := by
  have h0 := h 0 (by simp)
  have h1 : Nat.lcm n (n + 0) > Nat.lcm n (n + 0 + 1) := h0
  simp at h1
  have h2 : n > 0 := hn
  have h3 : Nat.lcm n (n + 1) = n * (n + 1) := by
    have h1' : Nat.gcd n (n + 1) = 1 := by
      simp [Nat.gcd_comm]
    rw [show Nat.lcm n (n + 1) = (n * (n + 1)) / Nat.gcd n (n + 1) by rw [Nat.lcm]]
    rw [h1']
    all_goals simp
  rw [h3] at h1
  nlinarith [show 0 < (n : ℕ) from hn, show 0 < (n + 1 : ℕ) from by linarith]
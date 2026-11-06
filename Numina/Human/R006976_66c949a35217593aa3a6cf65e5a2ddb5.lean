import Mathlib

/- Determine all integers $s \geq 4$ for which there exist positive integers $a, b, c, d$ such that $s=a+b+c+d$ and $s$ divides $a b c+a b d+a c d+b c d$. -/
theorem number_theory_246769 :
    {s : ℕ | 4 ≤ s ∧ ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ s = a + b + c + d ∧ s ∣ a * b * c + a * b * d + a * c * d + b * c * d} = {s : ℕ | ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ s = a * b} := by
  -- Break the goal into two parts.
  ext s
  simp
  apply Iff.intro
  . -- Show that the condition implies that s is composite.
    intro ⟨h₀, a, ha, b, hb, c, hc, d, hd, h₁, h₂⟩
    -- It suffices to show that s is not a prime number.
    suffices ¬Nat.Prime s by
      contrapose! this
      rw [Nat.prime_def]
      simp [show 2 ≤ s by omega]
      -- Show that m ∣ s → m = 1 ∨ m = s.
      intro m hm
      obtain ⟨n, hm⟩ := hm
      by_contra! hm'
      -- Show that m, n > 1.
      have hm'' : m > 1 := by
        by_contra!
        replace this : m = 0 := by
          omega
        simp [this, hm] at h₀
      have hn : n > 1 := by
        by_contra!
        interval_cases n
        . -- Contradiction when n = 0.
          simp [hm] at h₀
        . -- Contradiction also when n = 1.
          simp [hm] at hm'
      specialize this m hm'' n hn
      simp [hm] at this
    -- Assume on the contrary that s is a prime number, then we derive a contradiction.
    by_contra! hs
    -- Note that s ∣ (a + b)(a + c)(a + d) in this case.
    have h₃ : s ∣ (a + b) * (a + c) * (a + d) := by
      -- Show that (a + b)(a + c)(a + d) = a * b * c + a * b * d + a * c * d + b * c * d + a²s.
      rw [show (a + b) * (a + c) * (a + d) = a * b * c + a * b * d + a * c * d + b * c * d  + a ^ 2 * s by rw [h₁]; ring_nf]
      rw [<-Nat.dvd_add_iff_left]
      . exact h₂
      . apply Nat.dvd_mul_left
    -- Since s is a prime, we have s ∣ a + b, s ∣ a + c or s ∣ a + d.
    iterate 2 rw [Nat.Prime.dvd_mul hs] at h₃
    rcases h₃ with ((h₃ | h₃) | h₃)
    all_goals
      -- If s ∣ a + b or a + c or a + d, then it divides something positive but smaller number, contradiction.
      rw [h₁] at h₃
      apply Nat.le_of_dvd at h₃
      omega
      omega
  . -- Show that composite numbers satisfy the condition.
    intro ⟨a', ha', b', hb', h₀⟩
    simp [show 4 ≤ s by rw [h₀]; nlinarith]
    -- Use s = (w + x)(y + z) for some w + x = a' and y + z = b'. Specifically, let (x, y, z, w) = (a' - 1, b' - 1, 1, 1).
    -- Then, let (a, b, c, d) = (xy, xz, wy, wz).
    replace ha' : 0 < a' - 1 := by
      omega
    replace hb' : 0 < b' - 1 := by
      omega
    use (a' - 1) * (b' - 1), by positivity, a' - 1, ha', b' - 1, hb', 1, by norm_num
    simp
    rw [show a' = (a' - 1 + 1) by rw [Nat.sub_add_cancel (by omega)], show b' = (b' - 1 + 1) by rw [Nat.sub_add_cancel (by omega)]] at h₀
    refine ⟨?_, ?_⟩
    . -- Verify that s = a + b + c + d = (a' - 1)(b' - 1) + (a' - 1) + (b' - 1) + 1.
      linarith only [h₀]
    . -- Verify that s ∣ abc + abd + acd + bcd = (a' - 1)²(b' - 1)² + (a' - 1)²(b' - 1) + (a' - 1)(b' - 1)² + (a' - 1)(b' - 1) = (a' - 1)(b' - 1)s.
      replace h₀ := congr_arg (· * (a' - 1) * (b' - 1)) h₀
      simp only at h₀
      -- Note that abc + abd + acd + bcd = (a' - 1)(b' - 1)s.
      suffices s ∣ s * (a' - 1) * (b' - 1) by
        rw [h₀] at this
        convert this using 1
        ring_nf
      rw [mul_assoc]
      apply Nat.dvd_mul_right

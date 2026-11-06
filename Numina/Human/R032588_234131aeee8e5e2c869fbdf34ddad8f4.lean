import Mathlib

/- Given that $a$ is an odd multiple of $1183$, find the greatest common divisor of $2a^2+29a+65$ and $a+13$. -/
theorem number_theory_4844 (a k : ℕ) (h₀ : Odd k) (h₁ : a = 1183 * k) :
    Nat.gcd (2 * a ^ 2 + 29 * a + 65) (a + 13) = 26 := by
  -- Suffices to show that gcd (2 * a ^ 2 + 29 * a + 65, a + 13) = gcd (26, a + 13).
  have _ : Nat.gcd 26 (a + 13) = 26 := by
    -- a + 13 is an even multiple of 26.
    rw [show 1183 = 13 * 91 by norm_num, mul_assoc] at h₁
    rw [Nat.gcd_def]
    simp
    apply Nat.two_mul_div_two_add_one_of_odd at h₀
    replace h₀ : Even (91 * k + 1) := by
      rw [h₀.symm]
      rw [mul_add, add_assoc, show 91 * 1 + 1 = 2 * 46 by norm_num, <-mul_assoc, mul_comm 91 2, mul_assoc, <-mul_add]
      apply even_two_mul
    rw [even_iff_exists_two_mul] at h₀
    obtain ⟨b, h₀⟩ := h₀
    rw [h₁, show 13 * (91 * k) + 13 = 13 * (91 * k + 1) by ring_nf, h₀, <-mul_assoc]
    simp
  have _ : (2 * a + 3) * (a + 13) ≤ 2 * a ^ 2 + 29 * a + 65 := by
    ring_nf
    omega
  have h₂ : 2 * a ^ 2 + 29 * a + 65 - (2 * a + 3) * (a + 13) = 26 := by
    ring_nf
    rw [add_assoc, add_assoc, Nat.add_sub_add_right]
    norm_num
  -- gcd (2 * a ^ 2 + 29 * a + 65, a + 13) = gcd (2 * a ^ 2 + 29 * a + 65 - (2 * a + 3) * (a + 13), a + 13) = gcd (26, a + 13) = 26.
  calc
    Nat.gcd (2 * a ^ 2 + 29 * a + 65) (a + 13) = Nat.gcd (2 * a ^ 2 + 29 * a + 65 - (2 * a + 3) * (a + 13)) (a + 13) := by nth_rewrite 1 [show 2 * a ^ 2 + 29 * a + 65 = 2 * a ^ 2 + 29 * a + 65 - (2 * a + 3) * (a + 13) + (2 * a + 3) * (a + 13) by rwa [Nat.sub_add_cancel], Nat.gcd_comm]; nth_rewrite 2 [Nat.gcd_comm]; rw [Nat.gcd_add_mul_self]
    _ = Nat.gcd (26) (a + 13) := by rw [h₂]
    _ = 26 := by assumption

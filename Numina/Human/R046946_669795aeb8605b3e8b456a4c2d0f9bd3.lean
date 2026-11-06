import Mathlib

open Nat

/- Let $f(n)$ be a function that, given an integer $n$, returns an integer $k$, where $k$ is the smallest possible integer such that $k!$ is divisible by $n$. Given that $n$ is a multiple of 15, what is the smallest value of $n$ such that $f(n) > 15$? -/
theorem number_theory_15009 {f : ℕ → ℕ}
    (hf : ∀ n, IsLeast {x | n ∣ x ! } (f n)) :
    IsLeast {n | 15 ∣ n ∧ f n > 15} 255 := by
  rw [IsLeast, lowerBounds]; simp
  constructor
  · --verify 15 satisfy the condition
    obtain ⟨h1,_⟩ := hf 255
    simp at h1
    -- given 255 divide (f 255)!, let's argue 15 < f 255
    have h3: 15 < f (255) := by
      by_contra! hc
      -- notice that 255 = 17 x 15, so 17 ∣ 255
      have ht1: 17 ∣ 255 := by norm_num
      -- and 255 ∣ f 255, so 17 also divide f 255 !
      have ht2: 17 ∣ (f 255) ! := Nat.dvd_trans ht1 h1
      -- however, since 17 is prime, if 17 divide f 255 !, then 17 must <= f 255.
      have ht3: 17 ≤ f 255 := by
        have: Nat.Prime 17 := by norm_num
        apply (Nat.Prime.dvd_factorial this).mp ht2
      --thus we get a contradiction
      linarith [hc, ht3]
    exact ⟨(by norm_num), h3⟩
  · intro n hdvd hlt
    obtain ⟨h1,h2⟩ := hf n; simp at h1
    rw [lowerBounds] at h2; simp at h2
    -- and in this direction, we prove 255 is a lower bound. since 15 divide n, suppose n = 15r.
    rcases hdvd with ⟨r,hnr⟩
    -- we claim r > 14, because 15! contains 15 and all integer less than it as factors (3x5=15). if r <= 14, then n divide 15!, therefore f n ≤ 15, contradiction with the statement that f n > 15/
    have rgt: r > 14 := by
      have rnz: r ≠ 0 := by
        by_contra! rz
        rw [rz] at hnr; simp at hnr; rw [hnr] at h1; simp at h1
        have nh1: (f 0) ! ≠ 0 := factorial_ne_zero (f 0)
        rw [h1] at nh1; simp at nh1
      have rpos: 0 < r := by
        exact zero_lt_of_ne_zero rnz
      by_contra! hc
      have ht1: n ∣ 15 ! := by
        have hh1: 15 ! = 15 * 14 ! := rfl
        have hh2: r ∣ 14 ! := by
          exact dvd_factorial rpos hc
        rw [hnr, hh1]
        exact Nat.mul_dvd_mul_left 15 hh2
      have nhlt := h2 ht1
      linarith [nhlt, hlt]
    -- thus r ≥ 15, and we try each number ≥ 15.
    -- r = 15 fails. because 15 = 5x3, therefore 15x15 ∣ 15!, f n ≤ 15, contradiction.
    have rne15: r ≠ 15 := by
      by_contra! hc
      have dv15: n ∣ 15 ! := by
        rw [hnr, hc]
        exact dvd_of_mod_eq_zero rfl
      have := h2 dv15; linarith [this, hlt]
    -- also, since 16 = 8x2, 15x16 still divide 15!.
    have rne16: r ≠ 16 := by
      by_contra! hc
      have dv15: n ∣ 15 ! := by
        rw [hnr, hc]
        exact dvd_of_mod_eq_zero rfl
      have := h2 dv15; linarith [this, hlt]
    -- thereby r ≥ 17 and n ≥ 255
    have rge17: r ≥ 17 := by
      have: r > 15 := Nat.lt_of_le_of_ne rgt rne15.symm
      apply Nat.lt_of_le_of_ne this rne16.symm
    -- in the other direction, we already verify r=17 is OK. so here we don't need to prove a second time.
    rw [hnr]; linarith [rge17]
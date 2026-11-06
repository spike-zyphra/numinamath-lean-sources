import Mathlib

theorem algebra_98634 (x : ℝ) (m n : ℕ) (hx : x > 0) (hne : x ≠ 1 / 20 ∧ x ≠ 1 / 2)
(h : Real.logb (20 * x) (22 * x) = Real.logb (2 * x) (202 * x))
(hm: m > 0) (hn: n > 0) (hmn: m.Coprime n) (hmnx: Real.logb (20 * x) (22 * x) = Real.logb 10 ((m:ℝ) / n))
: m + n = 112 := by

  -- Unpack the non-equality conditions
  obtain ⟨hne₁, hne₂⟩ := hne

  -- define a to be log_(20x)(22x), from that deduce (20x)^a = 22x and (2x)^a = 202x
  set a := Real.logb (20 * x) (22 * x) with h'
  have ha₁ : (20 * x) ^ a = 22 * x := by
    refine (Real.logb_eq_iff_rpow_eq ?_ ?_ ?_).mp h'
    any_goals linarith
    intro hne₂'
    have : x = (1:ℝ) / 20 := by linarith
    contradiction
  have ha₂ : (2 * x) ^ a = 202 * x := by
    refine (Real.logb_eq_iff_rpow_eq ?_ ?_ ?_).mp h.symm
    any_goals linarith
    intro hne₁'
    have : x = (1:ℝ) / 2 := by linarith
    contradiction

  -- divide last two facts to get 10^a = 11/101
  have ha₃ : (10:ℝ) ^ a = 11 / 101 := by
    calc
      (10:ℝ)^a = (10:ℝ)^a * (2 * x)^a / (2 * x)^a := by field_simp
      _ = (10 * (2 * x))^a / (2 * x)^a := by
        congr
        refine Eq.symm (Real.mul_rpow ?_ ?_)
        norm_num
        linarith
      _ = (20*x)^a / (2*x)^a := by ring_nf
      _ = (22 * x) / (202 * x) := by rw[ha₁, ha₂]
      _ = 11 / 101 := by
        field_simp
        ring

  -- 10^a = m/n by hypothesis, so m * 101 = n * 11
  have ha₄ : (10:ℝ) ^ a = m / n := by
    refine (Real.logb_eq_iff_rpow_eq ?_ ?_ ?_).mp hmnx.symm
    any_goals norm_num
    apply div_pos
    all_goals norm_cast

  -- Solve for m and n such that m/n = 11/101 and m, n coprime
  have h1 : (m : ℝ) / n = (11 : ℝ) / 101 := by 
    linarith [ha₃, ha₄]

  have h2 : m * 101 = n * 11 := by
    have h' : (m : ℝ) * 101 = (n : ℝ) * 11 := by
      field_simp at h1 ⊢
      nlinarith
    norm_cast at h'

  have h3 : m.gcd n = 1 := by 
    exact hmn

  have h4 : m = 11 := by 
    -- From m * 101 = n * 11 and m.gcd n = 1, we can determine m = 11 and n = 101
    have h5 : m * 101 = n * 11 := h2
    have h6 : m.gcd n = 1 := h3
    -- Use Lean's number theory to solve
    have h7 : m ∣ n * 11 := by 
      use 101
      linarith
    have h8 : m ∣ 11 := by 
      -- Since m divides n * 11 and m.gcd n = 1
      have h9 : m ∣ n * 11 := h7
      have h10 : m.gcd n = 1 := h6
      have h11 : m ∣ 11 := by
        apply Nat.Coprime.dvd_of_dvd_mul_left h10 h9
      exact h11
    -- Since m divides 11, which is prime
    have h12 : m ≤ 11 := by 
      exact Nat.le_of_dvd (by norm_num) h8
    interval_cases m <;> omega

  -- Now n can be determined 
  have h5 : n = 101 := by
    -- From m * 101 = n * 11 and m.gcd n = 1, we can determine m = 11 and n = 101
    have h4' : m * 101 = n * 11 := h2
    have h4 : m = 11 := h4
    nlinarith
  -- m and n coprimes such that m * 101 = n * 11
  omega
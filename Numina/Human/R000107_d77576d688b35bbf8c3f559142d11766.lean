import Mathlib

/-- (1) : Show that if $\( a \)$ and $\( b \)$ are positive integers with $\( d = (a, b) \)$, the equation $\( ax + by = c \)$ has no integer solutions if $\( d \nmid c \)$. -/
theorem number_theory_4620_1 (a b : ℕ) (c : ℤ) (hd : ¬ (a.gcd b : ℤ)∣ c)
  : ¬ ∃ x y, a * x + b * y = c := by
    contrapose! hd
    obtain ⟨x, y, hc⟩ := hd
    rw [←hc]
    exact Int.dvd_add (by apply Dvd.dvd.mul_right; norm_cast; simp [Nat.gcd_dvd_left])
      (by apply Dvd.dvd.mul_right;norm_cast; simp [Nat.gcd_dvd_right])

/-- (2) : Conversely, if $\( d \mid c \)$, then there are infinitely many integer solutions. Furthermore, if $\( (x_0, y_0) \)$ is a particular solution of the equation, all solutions can be expressed as:
$$
x = x_0 + \frac{b}{d} n, \quad y = y_0 - \frac{a}{d} n
$$
where $\( n \)$ is an integer.-/
theorem number_theory_4620_2 (a b : ℕ) (ha : a ≠ 0) (_ : b ≠ 0) (c x y : ℤ) (hd : (a.gcd b : ℤ)∣ c) (hc : a * x + b * y = c) :
  let e := c / a.gcd b;
  ∃ n : Int, x = (a.gcdA b * e) + b / a.gcd b * n ∧ y = (a.gcdB b * e) - a / a.gcd b * n := by
    intro e
    -- there exist integers x0 and y0 s.t. a * x0 + b * y0 = c
    have he : a * (a.gcdA b * e) + b * (a.gcdB b * e) = c := by
      simp [e]
      calc
        _ = ((a * (a.gcdA b) + b * a.gcdB b) ) * e := by ring
        _ = _ := by rw [←Nat.gcd_eq_gcd_ab a b]; simp [e]; exact Int.mul_ediv_cancel' hd
    set x0 := a.gcdA b * e with hx0
    set y0 := a.gcdB b * e with hy0
    rw [←hc] at he
    -- Rearranging gives : $a * (x - x_0) = b * (y_0 - y)$
    have h1 : a * (x - x0) = b * (y0 - y) := by
      simp only [mul_sub]
      linarith
    -- Dividing both sides of this equation by the gcd of a and b. 
    have h2 : (a / a.gcd b) * (x - x0) = (b / a.gcd b)* (y0 - y) := by
      rw [mul_comm, show (a.gcd b : ℤ) = ((a : ℤ).gcd (b : ℤ) : ℤ) by norm_cast]
      rw [←Int.mul_ediv_assoc (x - x0) (@Int.gcd_dvd_left a b), mul_comm, h1]
      refine Int.mul_ediv_assoc' (y0 - y) ?h
      norm_cast
      exact Nat.gcd_dvd_right a b
    -- we know that $(\frac a d, \frac b d) = 1$, it follows that $\frac a d \mid (y_0 - y)$
    have h3 : (a / a.gcd b : ℤ) ∣ (y0 -y) := by
      have h3 : (a / a.gcd b : ℤ).gcd (b / a.gcd b) = 1 := by
        norm_cast
        refine Nat.coprime_div_gcd_div_gcd ?H
        exact Nat.gcd_pos_of_pos_left b (by positivity)
      have h4 : (a / a.gcd b : ℤ) ∣ (b / a.gcd b) * (y0 -y) := Dvd.intro (x - x0) h2
      have h5 := dvd_gcd_mul_of_dvd_mul h4
      simp [←Int.coe_gcd,h3] at h5
      exact h5
    obtain ⟨n, hn⟩ := h3
    --  Substituting y into the equation a * (x - x0) = b * (y - y0)
    have h4 : x = x0 + ↑b / ↑(a.gcd b) * n := by
      rw [hn, ←mul_assoc, ] at h1
      rw [←Int.mul_ediv_assoc b (show (a.gcd b : ℤ)∣ a by norm_cast; exact Nat.gcd_dvd_left a b)] at h1
      have : x - x0 = b * a / (a.gcd b) * n / a := by
        refine Int.eq_ediv_of_mul_eq_right (by positivity) h1
      have : x - x0 = b / a.gcd b * n := by
        rw [this]
        calc
          _ = a * (b / a.gcd b) * n / a := by
            congr 1; congr 1
            have : (a.gcd b : ℤ) ≠ 0 := by
              norm_cast; exact Nat.gcd_ne_zero_left ha
            refine Eq.symm (Int.eq_ediv_of_mul_eq_right (by norm_cast; exact Nat.gcd_ne_zero_left ha) ?_)
            rw [←mul_assoc]; nth_rw 2 [mul_comm]; rw [mul_assoc, ←Int.mul_ediv_assoc]
            rw [Int.mul_ediv_cancel_left b this]
            ring
            norm_cast
            exact Nat.gcd_dvd_right a b
          _ = _ := by refine Eq.symm (Int.eq_ediv_of_mul_eq_right (by norm_cast) (by ring))
      linarith
    have h3 : y = y0 - (a / a.gcd b) * n := by linarith
    exact ⟨n, ⟨h4, h3⟩⟩

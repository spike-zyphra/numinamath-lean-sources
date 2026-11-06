import Mathlib

/-If $\log_8{3}=p$ and $\log_3{5}=q$, then, in terms of $p$ and $q$, $\log_{10}{5}$ equals
$\mathrm{(A)\ } pq \qquad \mathrm{(B) \ }\frac{3p+q}{5} \qquad \mathrm{(C) \  } \frac{1+3pq}{p+q} \qquad \mathrm{(D) \  } \frac{3pq}{1+3pq} \qquad \mathrm{(E) \  }p^2+q^2$-/
theorem algebra_97515 {p q : ℝ} (hp : Real.logb 8 3 = p) (hq : Real.logb 3 5 = q) :
    Real.logb 10 5 = 3 * p * q / (1 + 3 * p * q) := by 
  have h1 : Real.logb 8 3 = Real.log 3 / Real.log 8 := by
    rw [Real.logb]
  -- We have $\log_{3}{8}=3\log_{3}{2}$,
  have h2 : Real.log 8 = 3 * Real.log 2 := by
    calc
      Real.log 8 = Real.log (2^3) := by norm_num
      _ = 3 * Real.log 2 := by simp [Real.log_pow]
  rw [h1] at hp
  -- We have $\frac{1}{p}=3\log_{3}{2}$,
  -- Thus $\log{3}=3p\log{2}$
  have h3 : Real.log 3 = 3 * p * Real.log 2 := by
    have h4 : Real.log 3 = 3 * p * Real.log 2 := by
      rw [h2] at hp
      field_simp at hp
      linarith
    exact h4
  have h5 : Real.logb 3 5 = Real.log 5 / Real.log 3 := by
    rw [Real.logb]
  rw [h5] at hq
  -- we have $q = \frac{\log{5}}{\log{3}}$
  -- Thus $\log{5}=3pq\log{2}$
  have h6 : Real.log 5 = 3 * p * q * Real.log 2 := by
    have h7 : Real.log 5 = q * Real.log 3 := by
      have h8 : Real.log 3 ≠ 0 := by
        apply ne_of_gt
        apply Real.log_pos
        norm_num
      field_simp at hq
      linarith
    rw [h3] at h7
    linarith
  have h9 : Real.log 2 ≠ 0 := by
    have h10 : Real.log 2 > 0 := by
      apply Real.log_pos
      norm_num
    linarith
  have h11 : Real.logb 10 5 = Real.log 5 / Real.log 10 := by 
    rw [Real.logb]
  have h12 : Real.log 10 = Real.log (2 * 5) := by 
    norm_num
  rw [h11, h12]
  have h13 : Real.log (2 * 5) = Real.log 2 + Real.log 5 := by
    rw [Real.log_mul (by linarith) (by linarith)]
  have h14 : Real.log 2 + Real.log 5 = Real.log (2 * 5) := by
    rw [h13]
  have h15 : (1 + 3 * p * q) ≠ 0 := by
    by_contra h
    have h16 : Real.log 2 = 0 := by
      have h17 : Real.log 2 * (1 + 3 * p * q) = Real.log (2 * 5) := by
        linarith [h6, h14]
      rw [h] at h17
      have h18 : Real.log (2 * 5) = 0 := by linarith [h17]
      have h19 : Real.log (2 * (5 : ℝ)) > 0 := by
        apply Real.log_pos
        norm_num
      linarith
    contradiction
  -- so finally: $\log_{10}{5}=\frac{3pq\log{2}}{1+3pq\log{2}}=\frac{3pq}{1+3pq}$
  have h17 : Real.log 2 = Real.log (2 * 5) / (1 + 3 * p * q) := by 
    have h18 : Real.log (2 * 5) = (1 + 3 * p * q) * Real.log 2 := by
      linarith [h6, h14]
    field_simp [h15]
    linarith
  have h19 : Real.log 5 = 3 * p * q * (Real.log (2 * 5) / (1 + 3 * p * q)) := by
    rw [h6, h17]
  have h20 : Real.log (2 * 5 : ℝ) ≠ 0 := by
    have h21 : Real.log (2 * 5 : ℝ) > 0 := by
      apply Real.log_pos
      norm_num
    linarith
  rw [h19]
  field_simp [h20, h15]
  linarith
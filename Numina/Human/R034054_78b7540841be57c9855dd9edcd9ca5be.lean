import Mathlib

/- 6. (1993 3rd Macau Mathematical Olympiad) The sequence of positive numbers $\left\{a_{n}\right\}$ satisfies

$$

a_{1}=a_{2}=1, a_{3}=997, a_{n+3}=\frac{1993+a_{n+2} \cdot a_{n+1}}{a_{n}}, n \in \mathbf{N} \text {. }

$$


Prove that all $a_{n}$ are integers. -/
theorem algebra_231729 (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (h1 : a 1 = 1) (h2 : a 2 = 1) (h3 : a 3 = 997)
    (h4 : ∀ n, a (n + 3) = (1993 + a (n + 2) * a (n + 1)) / a n) :
    ∀ n, ∃ m : ℤ, a n = m := by
  -- let's show a 0 = 2
  have h0 : a 0 = 2 := by
    specialize h4 0; simp [h1, h2, h3] at h4
    norm_num at h4
    apply congr_arg (fun x => x * (a 0)/997) at h4
    rw [div_mul, div_self (by linarith [ha 0])] at h4
    norm_num at h4; assumption
  -- let's remove the fraction from h4
  have h4' : ∀ n, a (n + 3) * a n = 1993 + a (n + 2) * a (n + 1) := by
    intro n
    specialize h4 n; rw[h4]
    rw [div_mul, div_self (by linarith [ha n])]; ring_nf
  -- let's subtract h4' (n+1) from h4' n
  have h5 : ∀ n, a (n + 3) * a n - a (n + 4) * a (n+1) = 1993 + a (n + 2) * a (n + 1) - (1993 + a (n + 3) * a (n + 2)) := by
    intro n
    rw [h4' (n+1), h4' n]
  simp at h5
  -- we can simplify this by grouping terms
  have h6 : ∀ n, a (n+4) + a (n+2) = a (n+3) / a (n+1) * (a (n+2) + a n) := by
    intro n; specialize h5 n
    apply congr_arg (fun t => (t + a (n + 4) * a (n + 1) + a (n + 3) * a (n + 2)) / (a (n+1))) at h5
    -- simplify
    conv_lhs at h5 =>
      calc (a (n + 3) * a n - a (n + 4) * a (n + 1) + a (n + 4) * a (n + 1) + a (n + 3) * a (n + 2)) / a (n + 1)
      _ = a (n + 3) * (a n + a (n + 2)) / a (n + 1) := by ring_nf
      _ = a (n + 3) / a (n + 1) * (a (n + 2) + a n) := by ring_nf
    conv_rhs at h5 =>
      calc (a (n + 2) * a (n + 1) - a (n + 3) * a (n + 2) + a (n + 4) * a (n + 1) + a (n + 3) * a (n + 2)) / a (n + 1)
      _ = (a (n + 2) + a (n + 4)) * (a (n + 1) / a (n + 1)) := by ring_nf
      _ = (a (n + 2) + a (n + 4)) := by rw [div_self (by linarith [ha (n+1)]), mul_one]
      _ = a (n + 4) + a (n + 2) := by ring_nf
    exact h5.symm
  -- we can telescope h6
  have h7: ∀ n, a (2*n+4) + a (2*n+2) = 3 * a (2*n+3) := by
    intro n
    induction n with
    |zero => simp; rw [h4 1]; simp; rw [h3, h2, h1]; norm_num
    |succ n ih =>
      calc  a (2 * (n + 1) + 4) + a (2 * (n + 1) + 2)
      _ = a (2 * (n + 1) + 3) / a (2 * (n + 1) + 1) * (a (2 * (n + 1) + 2) + a (2 * (n + 1))) := by rw [h6 (2 * (n+1))]
      _ = a (2 * (n + 1) + 3) / a (2 * (n + 1) + 1) * (a (2 * n + 4) + a (2 * n + 2)) := by ring_nf
      _ = a (2 * (n + 1) + 3) / a (2 * (n + 1) + 1) * 3 * a (2*n+3) := by rw [ih]; ring_nf
      _ = a (2 * (n + 1) + 3) * 3 := by ring_nf; rw [mul_assoc (a (5 + n * 2)), mul_inv_cancel₀ (by linarith [ha (3+n*2)]), mul_one];
      _ = 3 * a (2 * (n + 1) + 3) /- goal -/ := by ring_nf

  have h7': ∀ n, a (2*n+4) = 3 * a (2*n+3) - a (2*n+2) := by intro n; linarith [h7 n]
  -- and similarly for odd numbers
  have h8: ∀ n, a (2*n+5) + a (2*n+3) = 998 * a (2*n+4) := by
    intro n
    induction n with
    |zero => simp; rw [h4 2, h4 1]; simp; rw [h3, h2, h1]; norm_num
    |succ n ih =>
      calc  a (2 * (n + 1) + 5) + a (2 * (n + 1) + 3)
      _ = a (2 * (n + 1) + 4) / a (2 * (n + 1) + 2) * (a (2 * (n + 1) + 3) + a (2 * (n + 1) + 1)) := by rw [h6 (2 * (n+1) + 1)]
      _ = a (2 * (n + 1) + 4) / a (2 * (n + 1) + 2) * (a (2 * n + 5) + a (2 * n + 3)) := by ring_nf
      _ = a (2 * (n + 1) + 4) / a (2 * (n + 1) + 2) * 998 * a (2*n+4) := by rw [ih]; ring_nf
      _ = a (2 * (n + 1) + 4) * 998 := by ring_nf; rw [mul_assoc (a (6 + n * 2)), mul_inv_cancel₀ (by linarith [ha (4+n*2)]), mul_one];
      _ = 998 * a (2 * (n + 1) + 4) /- goal -/ := by ring_nf
  have h8': ∀ n, a (2*n+5) = 998 * a (2*n+4) - a (2*n+3) := by intro n; linarith [h8 n]
  -- we can now prove the main result by induction
  intro n
  induction' n using Nat.strong_induction_on with n ih
  match n with
  |0 => use 2; trivial
  |1 => use 1; simp [h1]
  |2 => use 1; simp [h2]
  |3 => use 997; trivial
  |n'+4 =>
    -- split by cases depending on even
    have hevenodd := Nat.even_or_odd n'
    cases' hevenodd with heven hodd
    · unfold Even at heven; obtain ⟨r, hr⟩ := heven;
      conv_rhs at hr =>
        calc r+r
        _ = 2*r := by ring_nf
      rw [hr, h7' r]
      obtain ⟨ml, hml⟩ := ih (2 * r + 3) (by linarith)
      obtain ⟨mr, hmr⟩ := ih (2 * r + 2) (by linarith)
      use 3*ml-mr
      rw [hml, hmr]
      norm_cast
    · unfold Odd at hodd; obtain ⟨r, hr⟩ := hodd;
      rw [hr, h8' r]
      obtain ⟨ml, hml⟩ := ih (2 * r + 4) (by linarith)
      obtain ⟨mr, hmr⟩ := ih (2 * r + 3) (by linarith)
      use 998*ml-mr
      rw [hml, hmr]
      norm_cast
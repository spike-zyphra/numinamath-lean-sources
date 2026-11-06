import Mathlib

/- Find all values of $k$ so that the graphs of $x^2 + y^2 = 4 + 12x + 6y$ and $x^2 + y^2 = k + 4x + 12y$ intersect.  Enter your answer using interval notation. -/
theorem algebra_20790 (k : ℝ) :
    (∃ x y, x^2 + y^2 = 4 + 12 * x + 6 * y ∧ x^2 + y^2 = k + 4 * x + 12 * y) ↔
    (k ∈ Set.Icc (-36) 104) := by
  constructor
  . {
    intro h
    obtain ⟨x, y, h1, h2⟩ := h

    -- sub the first equation from the second
    have h3 := calc
      -(y * 6) + (-k + 4 + 8 * x)  = -k + 4 + 8 * x - 6 * y := by ring_nf
      _ = (4 + 12 * x + 6 * y) - (k + 4 * x + 12 * y) := by ring_nf
      _ = 0 := by rw [<- h2, <- h1]; simp
    replace h3 : y * 6 = -k + 4 + 8 * x := neg_add_eq_zero.1 h3
    replace h3 : y = (-k + 4 + 8 * x) / 6 := eq_div_of_mul_eq (by simp) h3

    -- substitute y in the first equation
    rw [h3, <- neg_add_eq_zero] at h1
    ring_nf at h1
    replace h1 : (-25 / 9) * (x * x) + ((164 / 9) + k * (4 / 9)) * x + (68 / 9 + k * (-7 / 9) + k ^ 2 * (-1 / 36)) = 0 := by rw [<-h1]; ring_nf
    let a := (-25 / 9:ℝ )
    let b := ((164 / 9) + k * (4 / 9))
    let c := (68 / 9 + k * (-7 / 9) + k ^ 2 * (-1 / 36))
    have discrim': discrim a b c = - ((k-104) * (k+36) / 9) := by
      unfold discrim
      simp [a, b, c]
      ring_nf

    -- the discriminant is non-negative
    have discrim'' : discrim a b c = (2 * a * x + b) ^ 2 := (quadratic_eq_zero_iff_discrim_eq_sq (by norm_num) x).1 h1
    replace discrim_ge_0 : 0 ≤ discrim a b c := by
      rw [discrim'']
      exact sq_nonneg _
    rw [discrim'] at discrim_ge_0
    have discrim_ge_0 : (k - 104) * (k + 36) ≤ -0 * 9 := (div_le_iff₀ (by simp)).1 (le_neg.1 discrim_ge_0)
    simp at discrim_ge_0

    -- solving quadratic inequalities
    have h4 := mul_nonpos_iff.1 discrim_ge_0
    cases h4 with
    | inl h5 => {
      exfalso
      linarith
    }
    | inr h5 => {
      simp
      simp at h5
      constructor <;> linarith
    }
  }
  . {
    intro h
    simp at h

    -- write the root of the quadratic equation
    let x := ((164 / 9) + k * (4 / 9) + Real.sqrt (-((k-104) * (k+36) / 9))) / (50 / 9)
    let y := (-k + 4 + 8 * x) / 6

    -- prove the things in the sqrt is non-negative
    have discrim_ge_0: (k - 104) * (k + 36) ≤ -0 * 9 := by
      simp
      have h1: k-104 ≤ 0 := by linarith
      have h2: 0 ≤ k+36 := by linarith
      exact mul_nonpos_of_nonpos_of_nonneg h1 h2

    replace discrim_ge_0 : 0 ≤ -((k-104) * (k+36) / 9) := le_neg.1 ((div_le_iff₀ (by simp)).2 discrim_ge_0)
    have discrim_eq:  -((k-104) * (k+36) / 9) =  416 + k * (68 / 9) + k ^ 2 * (-1 / 9) := by ring_nf
    rw [discrim_eq] at discrim_ge_0

    -- prove the root is correct
    have h1 : x^2 + y^2 = 4 + 12 * x + 6 * y := by
      simp [x, y]
      ring_nf
      rw [Real.sq_sqrt discrim_ge_0]
      ring_nf
    have h2: x ^ 2 + y ^ 2 = k + 4 * x + 12 * y := by
      rw [h1]
      simp [y]
      ring_nf

    exact ⟨x, y, h1, h2⟩
  }

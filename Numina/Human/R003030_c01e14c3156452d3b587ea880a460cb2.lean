import Mathlib

/- 9 Given that the function $f(x)$ is defined on $\mathbf{R}$, and satisfies: (1) $f(x)$ is an even function; (2) For any $x \in \mathbf{R}$, $f(x+4)=f(x)$, and when $x \in[0,2]$, $f(x)=x+2$. Then the distance between the two closest intersection points of the line $y=4$ and the graph of the function $f(x)$ is $\qquad$ -/
theorem algebra_146641 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x)
    (h₁ : ∀ x, f (x + 4) = f x) (h₂ : ∀ x ∈ Set.Icc 0 2, f x = x + 2) :
    IsLeast {d | ∃ x y, x ≠ y ∧ d = |x - y| ∧ f x = 4 ∧ f y = 4} 4 := by
  have f_eq_4_iff x : f x = 4 ↔ /- x % 4 = 2 -/ ∃ i : ℤ, x = 4 * i + 2 := by
    have f_2_eq_4 : f 2 = 4 := by
      convert h₂ 2 (by simp)
      norm_num
    have periodic_4 : f.Periodic 4 := h₁
    have periodic_4_i := periodic_4.int_mul
    constructor
    . intro f_x_eq_4
      let i := ⌊x / 4⌋
      --let r := x % 4
      let r := x - 4 * i
      have r_pos : r ≥ 0 := by
        unfold r i
        suffices ⌊x / 4⌋ ≤ x / 4 by
          linarith
        exact Int.floor_le (x / 4)
      have r_lt_4 : r < 4 := by
        unfold r i
        suffices x / 4 < ⌊x / 4⌋ + 1 by
          linarith
        exact Int.lt_floor_add_one (x / 4)
      have := periodic_4_i i r
      rw [show r + i * 4 = x by ring] at this
      rw [this] at f_x_eq_4
      by_cases w_r_lt_2 : r ≤ 2
      . have : r ∈ Set.Icc 0 2 := by
          simp
          exact ⟨r_pos, w_r_lt_2⟩
        have := h₂ r this
        have : r = 2 := by
          linarith
        use i
        unfold r at this
        linarith
      . /- not needed
        have : r ∈ Set.Ioo 2 4 := by
          simp
          constructor
          . linarith
          . exact r_lt_4
         -/
        have : f r = f (4 - r) := by
          have := h₁ (r - 4)
          simp at this
          have := h₀ (r - 4)
          simp at this
          linarith
        have : 4 - r ∈ Set.Icc 0 2 := by
          simp
          constructor <;>
          . linarith
        have : f r = 6 - r := by
          have := h₂ (4 - r) this
          linarith
        have : r = 4 := by
          linarith
        exfalso
        linarith
    . rintro ⟨i, rfl⟩
      convert periodic_4_i i 2 using 1
      . congr 1
        ring
      . exact f_2_eq_4.symm
  have : {d | ∃ x y, x ≠ y ∧ d = |x - y| ∧ f x = 4 ∧ f y = 4} = { (4 * n : ℝ) | (n : ℕ) (_ : n ≠ 0) } := by
    ext z
    simp only [Set.mem_setOf_eq, exists_prop]
    constructor
    . rintro ⟨x, y, x_ne_y, rfl, f_x_eq_4, f_y_eq_4⟩
      have := (f_eq_4_iff x).mp f_x_eq_4
      rcases this with ⟨i, rfl⟩
      have := (f_eq_4_iff y).mp f_y_eq_4
      rcases this with ⟨j, rfl⟩
      have : i ≠ j := by
        norm_cast at x_ne_y
        omega
      use (i - j).natAbs, (by omega)
      simp

      /- original more complicated approach
      norm_cast
      --zify
      --norm_cast
      have : (↑(4 * (i - j).natAbs) : ℝ) = ((4 * (i - j).natAbs : ℤ) : ℝ) := by
        norm_cast
      rw [this]
      norm_cast
      have : |4 * i - 4 * j| = 4 * |i - j| := by
        rw [show 4 * i - 4 * j = 4 * (i - j) by ring]
        --omega
        exact IsAbsoluteValue.abv_mul abs 4 (i - j)
      rw [this]
      push_cast
      congr
       -/

      have : |(4 * i - 4 * j : ℝ)| = 4 * |(i - j : ℝ)| := by
        rw [show (4 * i - 4 * j : ℝ) = 4 * (i - j) by ring]
        conv_rhs => rw [show (4 : ℝ) = |4| by simp]
        exact abs_mul 4 (i - j : ℝ)
      rw [this]
      congr
      norm_cast
      exact Nat.cast_natAbs (i - j)
    . rintro ⟨n, n_nonzero, rfl⟩
      --rw [f_eq_4_iff]
      simp only [f_eq_4_iff]
      use 4 * n + 2, 2
      constructor
      . norm_cast
        --linarith
        omega
      . constructor
        . simp
          norm_cast
        . constructor
          . use n
            rfl
          . use 0
            norm_num
  rw [this]
  constructor
  . simp
  . simp [lowerBounds]

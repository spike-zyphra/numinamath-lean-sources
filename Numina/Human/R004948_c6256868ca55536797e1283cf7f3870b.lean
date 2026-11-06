import Mathlib

/- Bepaal alle paren positieve gehele getallen $(x, y)$ waarvoor

$$
x^{3}+y^{3}=4\left(x^{2} y+x y^{2}-5\right) .
$$ -/
theorem algebra_604763 (x y : ℤ) (hx : 0 < x) (hy : 0 < y):
    (x^3 + y^3 = 4 * (x^2 * y + x * y^2 - 5)) ↔
    ((x, y) = (1, 3) ∨ (x, y) = (3, 1)) := by
  constructor
  · intro heq
    -- rearrange the equation
    have heq': (x+y)*(x^2-x*y+y^2) = 4*x*y*(x+y) - 20 := by
      -- notice that x^3+y^3 = (x+y)(x^2-xy+y^2)
      have: x^3+y^3 = (x+y)*(x^2-x*y+y^2) := by ring
      rw [← this, heq]
      ring
    -- therefore x+y divide 20
    have hdvd1: x+y ∣ 20 := by
      have h1: x+y ∣ 4*x*y*(x+y) - 20 := by
        rw [← heq']
        apply Int.dvd_mul_right
      have h2: x+y ∣ 4*x*y*(x+y) := by
        apply Int.dvd_mul_left
      exact (Int.dvd_iff_dvd_of_dvd_sub h1).mp h2
    -- from x^3 + y^3 = 4 ..., x^3+y^3 must be even.
    -- that's to say, x+y is even.
    have evenxy: Even (x+y) := by
      have h1: Even (x^3+y^3) := by
        rw [heq]
        refine Even.mul_right ?_ _
        exact Int.even_iff.mpr rfl
      rw [Int.even_add] at h1
      -- easy to show x+y and x^3+y^3 have same parity
      by_cases hx: Odd x
      · rw [← Int.not_odd_iff_even, ← Int.not_odd_iff_even] at h1
        have h2: Odd (x^3) := Odd.pow hx
        have h3: Odd (y^3) := by tauto
        have h4: Odd y := Int.Odd.of_mul_right h3
        exact Odd.add_odd hx h4
      · rw [Int.not_odd_iff_even] at hx
        have h2: Even (x^3) := (Int.even_pow' (by norm_num)).mpr hx
        have h3: Even (y^3) := h1.mp h2
        rw [Int.even_pow] at h3
        apply Even.add hx h3.left
    -- therefore x+y = 2,4,10,20.
    have xyeq: x+y = 2 ∨ x+y = 4 ∨ x+y = 10 ∨ x+y = 20 := by
      have: ∀n:ℤ, 0 < n → n ≤ 20 → n ∣ 20 → Even n →
        (n=2 ∨ n=4 ∨ n=10 ∨ n=20) := by decide
      apply this _ (add_pos hx hy) ?_ hdvd1 evenxy
      apply Int.le_of_dvd (by norm_num) hdvd1
    -- notice that x^2-xy+y^2 = (x+y)^2-3xy
    replace heq: (x+y)*((x+y)^2-3*(x*y)) = 4*(x+y)*(x*y) - 20 := by
      nlinarith [heq']
    rcases xyeq with eq2 | eq4 | eq10 | eq20
    · -- x+y = 2, then x = 1, y = 1.
      have xeq: x = 1 := by omega
      have yeq: y = 1 := by omega
      -- substitute back, contradiction.
      simp [xeq, yeq] at heq
    · -- x+y = 4.
      -- we have 16 - 3xy = 4xy - 5
      have h1: 16 - 3*x*y = 4*x*y - 5 := by
        rw [eq4] at heq
        linarith [heq]
      -- therefore xy = 3.
      have h2: x*y = 3 := by
        linarith [h1]
      -- exactly the solution.
      -- xy = 3, solutions are x=1,y=3 and x=3,y=1.
      simp only [Prod.mk.injEq]
      replace h1: y ∣ 3 := by
        rw [← h2]; apply Int.dvd_mul_left
      replace h2: y = 1 ∨ y = 3 := by
        clear * - h1 hy
        have := Int.le_of_dvd (by norm_num) h1
        revert h1; revert this hy y
        decide
      rcases h2 with y1 | y3
      all_goals omega
    · -- x+y = 10
      -- we have 100 - 3xy = 4xy - 2
      have h1: 100 - 3*x*y = 4*x*y - 2 := by
        rw [eq10] at heq
        linarith [heq]
      have h2: 7*(x*y) = 102 := by
        linarith [h1]
      -- impossible for 7xy = 102
      have: (7:ℤ) ∣ 102 := by
        use x*y
        rw [h2]
      norm_num at this
    · -- x + y = 20
      -- we have 400 - 3xy = 4xy - 1
      have h1: 400 - 3*(x*y) = 4*(x*y) - 1 := by
        rw [eq20] at heq
        linarith [heq]
      have h2: 7*(x*y) = 401 := by
        linarith [h1]
      -- impossible for 7 divide 401.
      have: (7:ℤ) ∣ 401 := by
        use (x*y)
        rw [h2]
      norm_num at this
  · -- verification
    simp only [Prod.mk.injEq]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals norm_num
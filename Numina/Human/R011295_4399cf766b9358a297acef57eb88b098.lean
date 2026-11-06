import Mathlib

/- 3. (7 points) The graph of a reduced quadratic trinomial is shown in the figure (the y-axis is erased, the distance between adjacent marked points is 1). What is the discriminant of this trinomial?

![](https://cdn.mathpix.com/cropped/2024_05_06_7217c23a0b23cf0b4657g-1.jpg?height=306&width=576&top_left_y=2331&top_left_x=820) 

The graph is saying: two roots of the trinomial $x_1$ and $x_2$, satisfty $|x_1 - x_2|=2$ -/
theorem algebra_106170 (x y b c : ℝ) :
  let isRoot (x : ℝ) := x^2 + b * x + c = 0;
  let D := b^2 - 4*c ;
  D > 0 → isRoot x → isRoot y → x - y = 2 → D = 4 :=
by
  intro isRoot D Dpos xr yr Dxy
  -- First we show that, x and y are roots, following the formula.
  have xin : x ∈ ({(- b + Real.sqrt D)/2, (- b - Real.sqrt D)/2} : Set _) := by
    simp[D]
    simp [isRoot] at xr
    have : (x - (-b + Real.sqrt (b^2 - 4 * c)) / 2)
         * (x - (-b - Real.sqrt (b^2 - 4 * c)) / 2) = 0 := by
      nlinarith
        [ Real.sqrt_nonneg (b^2 - 4 * c)
        , Real.sq_sqrt
            (show 0 ≤ b^2 - 4 * c by
                nlinarith [sq_nonneg (x), sq_nonneg (x + b / 2)])
        ]
    cases (mul_eq_zero.mp this)
    . left
      linarith
    . right
      linarith
  have yin : y ∈ ({(- b + Real.sqrt D)/2, (- b - Real.sqrt D)/2} : Set _) := by
    simp[D]
    simp [isRoot] at yr
    have : (y - (-b + Real.sqrt (b^2 - 4 * c)) / 2)
      * (y - (-b - Real.sqrt (b^2 - 4 * c)) / 2) = 0 := by
      nlinarith
      [ Real.sqrt_nonneg (b^2 - 4 * c)
      , Real.sq_sqrt
        (show 0 ≤ b^2 - 4 * c by
          nlinarith [sq_nonneg (y), sq_nonneg (y + b / 2)])
      ]
    cases (mul_eq_zero.mp this)
    . left
      linarith
    . right
      linarith
  have xgty : x > y := by linarith
  have rgt : (- b + Real.sqrt D)/2 > (- b - Real.sqrt D)/2 := by
    refine (div_lt_div_iff_of_pos_right ?_).mpr ?_
    simp
    rw [show - b - √D = - b + - √D by linarith]
    refine (add_lt_add_iff_left (-b)).mpr ?_
    have : √ D > 0 := Real.sqrt_pos_of_pos Dpos
    linarith
  -- Then we get the value of x and y from the relation.
  have : x = (- b + Real.sqrt D)/2 ∧ y = (- b - Real.sqrt D)/2 := by
    simp at xin yin
    rcases xin with hx | hx <;> rcases yin with hy | hy <;>
    (
      try simp [hx, hy] at xgty
      <;> try simp [hx, hy]
      <;> try linarith
    )
  rw [this.1, this.2] at Dxy
  apply_fun (fun x => x ^ 2) at Dxy
  have : (√D) ^ 2 = D := by refine Real.sq_sqrt ?_; linarith
  ring_nf at Dxy
  rw [show b^2 - c*4 = D by simp[D]; linarith, this] at Dxy
  ring_nf at Dxy
  ring_nf
  assumption

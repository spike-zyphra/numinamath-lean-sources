import Mathlib

/- Let the function $f: \mathbb{Z} \rightarrow \mathbb{Z}$ take only integer inputs and have integer outputs. For any integers $x$ and $y, f$ satisfies

$$
f(x)+f(y)=f(x+1)+f(y-1)
$$

If $f(2016)=6102$ and $f(6102)=2016$, what is $f(1) ?$ -/
theorem algebra_609605 (f: ℤ → ℤ)
  (h1: f 2016 = 6102)
  (h2: f 6102 = 2016)
  (h3: ∀ x y: ℤ, f x + f y = f (x + 1) + f (y - 1)) : f 1 = 8117 := by

  -- prove f is linear, beacuse $f(x+1) = - f(x) + f(y - 1) - f(y)$
  have f_linear: ∃ a b : ℤ, ∀ x : ℤ, f x = a * x + b := by
    use f 1 - f 0
    use f 0
    intro x
    induction x using Int.induction_on with
    | hz =>
      simp
    | hp x hx =>
      specialize h3 x 1
      simp at h3
      linear_combination hx - h3
    | hn x hx =>
      specialize h3 (-x - 1) 1
      simp at h3
      linear_combination hx + h3
  obtain ⟨a, b, hab⟩ := f_linear
  -- use f(2016) = 6102 and f(6102) = 2016 to solve for a and b
  have hab1 := hab 2016
  rw [h1] at hab1
  have hab2 := hab 6102
  rw [h2] at hab2
  have ha : a = -1 := by linarith
  rw [ha] at hab1
  have hb : b = 8118 := by linear_combination -hab1
  rw [ha, hb] at hab

  -- solve for f(1)
  specialize hab 1
  rw [hab]
  ring

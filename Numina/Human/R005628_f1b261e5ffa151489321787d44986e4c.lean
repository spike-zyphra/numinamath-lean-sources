import Mathlib

/- How many pairs of real numbers (x, y) satisfy the equation
$$ y^4 - y^2 = xy^3 - xy = x^3y - xy = x^4 - x^2 = 0$$? -/
theorem algebra_609166 :
    { (x, y) : ℝ × ℝ | y ^ 4 - y ^ 2 = 0 ∧ x * y ^ 3 - x * y = 0
     ∧ x ^ 3 * y - x * y = 0 ∧ x ^ 4 - x ^ 2 = 0 }.ncard = 9 := by
  have h₀ : {(x, y) : ℝ × ℝ | y ^ 4 - y ^ 2 = 0 ∧ x * y ^ 3 - x * y = 0 ∧
      x ^ 3 * y - x * y = 0 ∧ x ^ 4 - x ^ 2 = 0}
      = {(1, 1), (-1, 1), (1, -1), (-1, -1), (0, 1), (0, -1), (1, 0),
      (-1, 0), (0, 0)} := by
    ext ⟨x, y⟩
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · intro h
      -- We can see that if they solve the first and fourth equations, 
      -- they are automatically solutions to the second and third equations.
      have hy : y^2 * (y-1)*(y+1) = 0 := by linarith
      have hx : x^2 * (x-1)*(x+1) = 0 := by linarith
      -- Hence, the solutions are just the $3^{2}=9$ points where $x, y$ can be any of $-1,0,1$.
      simp at hx
      simp at hy
      aesop
      left; linarith [h_3]
      left; linarith [h_3]
      left; apply And.intro; linarith [h_2]; linarith [h_3]
      right; left; linarith [h_2]
      right; right; left; apply And.intro; linarith [h_2]; linarith [h_3]
      right; left; linarith [h_1]
      right; left; apply And.intro; linarith [h_1]; linarith [h_3]
      right; right; right; left; apply And.intro; linarith [h_2]; linarith [h_1]
    · rintro (⟨rfl, rfl⟩| ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ ) <;> norm_num
  -- Next, we  count the number of elements in this set. 
  -- There are exactly $9$ such points: $(\pm 1, \pm 1)$, $(0, \pm 1)$, $(\pm 1, 0)$, and $(0, 0)$.
  rw [h₀]
  repeat rw [Set.ncard_insert_of_not_mem]
  simp
  repeat simp; simp; linarith
  simp
  constructor
  · intro _
    linarith
  · linarith
  simp
  repeat
    apply And.intro
    by_contra h
    have := Prod.mk.inj_iff.mp h
    linarith
  by_contra h
  have := Prod.mk.inj_iff.mp h
  linarith

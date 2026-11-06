import Mathlib

/- $12 \cdot 25$ Prove that for each real number $R_{0}$, the equation $x_{1}^{2}+x_{2}^{2}+x_{3}^{2}=x_{1} x_{2} x_{3}$ must have a solution $x_{1}, x_{2}, x_{3}$, all of which are integers greater than $R_{0}$.
（1st Zhejiang Province Mathematical Summer Camp, China, 1989） -/
theorem number_theory_111336 (R : ℝ) :
    ∃ x : Fin 3 → ℤ,
    (∀ i, x i > R) ∧
    x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = x 0 * x 1 * x 2 := by
  -- Show that for all natural numbers n, there exist a, b, c such that
  -- n + 2 < a < b < c and a^2 + b^2 + c^2 = a * b * c.
  have h (n : ℕ) : ∃ a b c : ℤ, n + 2 < a ∧ a < b ∧ b < c ∧ a^2 + b^2 + c^2 = a * b * c := by
    -- Proof by induction.
    induction n with
    | zero =>
      -- If n = 0 then take a = 3, b = 6, c = 15 and verify all required properties.
      use 3, 6, 15
      norm_num
    | succ n ih =>
      -- Suppose that there exist x, y, z such that
      -- n + 2 < x < y < z and x^2 + y^2 + z^2 = x * y * z.
      have ⟨x, y, z, hxn, hxy, hyz, h⟩ := ih
      -- Define a = y * z - x, b = a * z - y, c = a * b - z.
      set a := y * z - x
      set b := a * z - y
      set c := a * b - z
      use a, b, c
      -- We have z < 2 * z - x < y * z - x = a (because y > 2).
      have hza : z < a := calc
        z < 2 * z - x := by omega
        _ < y * z - x := by gcongr <;> omega
      -- We have a < a * 2 - y < a * z - y = b (because z > 2).
      have hab : a < b := calc
        a < a * 2 - y := by omega
        _ < a * z - y := by gcongr <;> omega
      -- We have b < 2 * b - z < a * b - z = c (because a > z > 2).
      have hbc : b < c := calc
        b < 2 * b - z := by omega
        _ < a * b - z := by gcongr <;> omega
      -- All required inequalities follow from the properties proved above.
      constructorm* _ ∧ _ <;> try omega
      -- a^2 + b^2 + c^2 = a * b * c follows from x^2 + y^2 + z^2 = x * y * z.
      linear_combination h
  -- Find a natural number n such that n > R.
  have ⟨n, hn⟩ := exists_nat_gt R
  -- Now we can get a, b, c such that R < n + 2 < a < b < c and a^2 + b^2 + c^2 = a * b * c.
  replace ⟨a, b, c, h⟩ := h n
  -- Define x(0) = a, x(1) = b, x(2) = c.
  let x : Fin 3 → ℤ
  | 0 => a
  | 1 => b
  | 2 => c
  use x
  -- We get x(0)^2 + x(1)^2 + x(2)^2 = a^2 + b^2 + c^2 = a * b * c = x(0) * x(1) * x(2).
  simp [x, h]
  intro i
  rify at h
  -- x(i) > R because c > b > a > R.
  fin_cases i <;> simp <;> linarith
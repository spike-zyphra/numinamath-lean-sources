import Mathlib

/- Trouver le nombre de solutions de $n^{2} m^{6}=180 t+2$ pour $n, m$ et $t$ des entiers positifs. -/
theorem number_theory_607208 :
    {(n, m, t) : ℕ × ℕ × ℕ | n > 0 ∧ m > 0 ∧ t > 0 ∧ n^2 * m^6 = 180 * t + 2}.encard = 0 := by
  -- We need to show that the set is empty
  simp
  ext ⟨n, m, t⟩
  simp
  -- We ignore the condition that n, m, t are positive
  rintro - - -
  -- It suffices to show that n^2 * m^6 ≠ 180t + 2 in Z/4Z
  apply_fun (Nat.cast (R := ZMod 4))
  -- 180 = 0 in Z/4Z
  simp [show 180 = (0 : ZMod 4) from rfl]
  -- We set x := n mod 4 and y := m mod 4
  generalize (n : ZMod 4) = x
  generalize (m : ZMod 4) = y
  -- Now we consider all the possible values of x and y in Z/4Z
  -- But x^2 * y^6 = 0 or 1 in Z/4Z always
  -- So we are done
  fin_cases x <;> fin_cases y <;> simp <;> decide

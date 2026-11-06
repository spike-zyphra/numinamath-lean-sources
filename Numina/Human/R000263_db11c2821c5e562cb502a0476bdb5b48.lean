import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Solve the equation, where  $x$  and  $y$  are positive integers:   $$  x^3-y^3=999 $$  -/
theorem number_theory_8741 :
  {(x, y) : ℕ × ℕ | 0 < x ∧ 0 < y ∧ x^3 - y^3 = 999} = {(10, 1), (12, 9)} := by
  -- divisors of 999 are {1, 3, 9, 27, 37, 111, 333, 999}
  have divisors999 : Nat.divisors 999 = {1, 3, 9, 27, 37, 111, 333, 999} := by native_decide
  ext z
  simp
  set x := z.1 with hx
  set y := z.2 with hy
  constructor
  . rintro ⟨hxpos, ⟨hypos, hxy⟩⟩
    -- Need these to perform subtraction of natural numbers.
    have : y^3 < x^3 := by
      by_contra h
      push_neg at h
      rw [Nat.sub_eq_zero_of_le h] at hxy
      norm_num at hxy
    have : y < x := by
      rwa [Nat.pow_lt_pow_iff_left (by norm_num)] at this
    -- We can factor the left-hand side using the difference of cubes formula:
    --  \[
    --  x^3 - y^3 = (x - y)(x^2 + xy + y^2)
    --  \]
    have xcube_sub_ycube : x^3-y^3 = (x-y)*(x^2+x*y+y^2) := by
      zify
      repeat rw [Nat.cast_sub (by linarith), Nat.cast_pow]
      ring
    -- It's clear that x-y is a divisor of 999.
    have x_sub_y_mem_divisors : x - y ∈ Nat.divisors 999 := by
      rw [Nat.mem_divisors]
      refine ⟨?_, by norm_num⟩
      rw [← hxy, xcube_sub_ycube]
      apply Nat.dvd_mul_right
    -- The factor pairs of 999 are:
    --    \[
    --    1 \cdot 999, \quad 3 \cdot 333, \quad 9 \cdot 111, \quad 27 \cdot 37
    --    \]
    -- 3. We will test each factor pair to see if it provides a solution in positive integers.
    rw [divisors999] at x_sub_y_mem_divisors
    simp at x_sub_y_mem_divisors
    rcases x_sub_y_mem_divisors with h1 | H
    -- Case (1): x-y=1
    . -- We can deduce that x^2+xy+y^2=999.
      have : x^2+x*y+y^2 = 999 := by rw [← hxy, xcube_sub_ycube, h1, Nat.one_mul]
      -- Substituting \(x = y + 1\):
      have x_eq_ysucc : x = y + 1 := by
        apply_fun (· + y) at h1
        rwa [Nat.sub_add_cancel (by linarith), Nat.add_comm] at h1
      rw [x_eq_ysucc] at this
      -- Simplify to 3(y^2+y) + 1 = 999.
      have : 3*(y^2+y) + 1 = 999 := by rw [← this]; ring
      -- There are no solution for above equation since y is integer.
      apply_fun (· % 3) at this
      rw [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul] at this
      norm_num at this
    rcases H with h1 | H
    -- Case (2): x-y=3
    . -- We can deduce that x^2+xy+y^2=333.
      have : x^2+x*y+y^2 = 333 := by
        rw [← Nat.mul_right_inj <| show 3 ≠ 0 by norm_num]
        nth_rw 1 [← h1]
        rw [← xcube_sub_ycube, hxy]
      -- Substituting \(x = y + 3\):
      have x_eq_y_add_three : x = y + 3 := by
        apply_fun (· + y) at h1
        rwa [Nat.sub_add_cancel (by linarith), Nat.add_comm] at h1
      rw [x_eq_y_add_three] at this
      -- Simplify to 3(y-9)(y+12)=0.
      have : 3*(y^2+3*y+3) = 333 := by rw [← this]; ring
      zify at this
      have : 3*((y : ℤ) - 9)*(y + 12) = 0 := by linear_combination this
      simp at this
      rcases this with h | h
      -- If y = 9, then the solution is (x,y)=(12,9).
      . have : y = 9 := by
          zify
          linear_combination h
        right
        ext
        . rw [← hx, x_eq_y_add_three, this]
        . rw [← hy, this]
      -- y = -12 which is contradictory to y>0.
      have : (0 : ℤ) < 0 := by
        nth_rw 2 [← h]
        linarith
      norm_num at this
    rcases H with h1 | H
    -- Case (3): x-y=9
    . -- We can deduce that x^2+xy+y^2=111.
      have : x^2+x*y+y^2 = 111 := by
        rw [← Nat.mul_right_inj <| show 9 ≠ 0 by norm_num]
        nth_rw 1 [← h1]
        rw [← xcube_sub_ycube, hxy]
      -- Substituting \(x = y + 9\):
      have x_eq_y_add_nine : x = y + 9 := by
        apply_fun (· + y) at h1
        rwa [Nat.sub_add_cancel (by linarith), Nat.add_comm] at h1
      rw [x_eq_y_add_nine] at this
      -- Simplify to 3(y-1)(y+10)=0.
      have : 3*(y^2+9*y+27)=111 := by rw [← this]; ring
      zify at this
      have : 3*((y : ℤ) - 1)*(y + 10) = 0 := by linear_combination this
      simp at this
      rcases this with h | h
      -- If y = 1, then the solution is (x,y)=(10,1).
      . have : y = 1 := by
          zify
          linear_combination h
        left
        ext
        . rw [← hx, x_eq_y_add_nine, this]
        . rw [← hy, this]
      -- y = -10 which is contradictory to y>0.
      have : (0 : ℤ) < 0 := by
        nth_rw 2 [← h]
        linarith
      norm_num at this
    rcases H with h1 | H
    -- Case (4): x-y=27
    . -- We can deduce that x^2+xy+y^2=37
      have : x^2+x*y+y^2 = 37 := by
        rw [← Nat.mul_right_inj <| show 27 ≠ 0 by norm_num]
        nth_rw 1 [← h1]
        rw [← xcube_sub_ycube, hxy]
      -- Substituting \(x = y + 27\):
      have x_eq_y_add_27 : x = y + 27 := by
        apply_fun (· + y) at h1
        rwa [Nat.sub_add_cancel (by linarith), Nat.add_comm] at h1
      rw [x_eq_y_add_27] at this
      -- Simplify to 3(y^2+27y+243)=37
      have : 3*(y^2+27*y+243)=37 := by rw [← this]; ring
      -- There are no solution for above equation since y is integer.
      apply_fun (· % 3) at this
      rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul] at this
      norm_num at this
    -- Case (5), (6), (7), (8) are impossible since x-y < x^2+xy+y^2
    have : (x - y) ^ 1 ≤  (x - y) ^ 2 := by
      apply Nat.pow_le_pow_right
      omega
      norm_num
    have : 0 < 3*x*y := by simp [hxpos, hypos]
    have : x - y < (x-y)^2 + 3*x*y := by linarith
    have : (x - y) ^ 2 < (x - y) * ((x-y)^2 + 3*x*y) := by
      nlinarith
    have : (x - y) ^ 2 < 999 := by
      convert this
      rw [← hxy, xcube_sub_ycube]
      congr 1
      zify
      rw [Nat.cast_sub (by linarith)]
      ring
    -- We can deduce x-y<33 from (x-y)^2 < 999.
    have : x - y < 33 := by nlinarith
    exfalso
    -- In case  (5), (6), (7), (8), we have x-y>33 which is contradictory to x-y<33.
    rcases H with h | h | h | h <;> rw [h] at this <;> norm_num at this
  -- verify solutions
  . intro hz
    rcases hz with hz | hz
    all_goals simp [hx, hy, hz]

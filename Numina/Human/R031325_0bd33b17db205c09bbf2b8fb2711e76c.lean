import Mathlib

/- 806. Prove that the equation


$$

3 x^{2}=16 y^{2}+8 y+5

$$


has no solutions in integers. -/
theorem number_theory_114867 (x y : ℤ) : ¬(3 * x ^ 2 = 16 * y ^ 2 + 8 * y + 5) := by
  --We prove by way of contradiction.
  --Assume 3 * x ^ 2 = 16 * y ^ 2 + 8 * y + 5
  by_contra h
  --Obtain 3 * x^2 = (4 * y + 1)^2 + 4 by completing the square on the RHS.
  have hcompSquare : 3 * x^2 = (4 * y + 1)^2 + 4 := by linarith
  --Show that 4 * y + 1 is not divisible by 3. We show this by way of contradiction.
  have hthreeNDiv : ¬ (3 ∣ 4 * y + 1)
  --Assume 3 ∣ 4 * y + 1
  by_contra h'
  --Then 3 ∣ (4 * y + 1)^2
  have hthreeDiv : 3 ∣ (4 * y + 1)^2 := by
    refine Dvd.dvd.pow h' ?_
    norm_num
  --Then it follows that 3 ∣ 3 * x^2 - 4.
  have hsubject : (4 * y + 1)^2 = 3 * x^2 - 4 := by linarith
  have hthreedivRest : 3 ∣ (3 * x^2 - 4) := by
    rw [←hsubject]
    exact hthreeDiv
  --Now, it follows that 3 ∣ 4 as 3 ∣ 3 * x^2
  have hthreeDivFour : 3 ∣ 4 := by
    refine Nat.dvd_of_mod_eq_zero ?_
    have : 4 = 3 * x^2 - (4 * y + 1)^2 := by linarith
    omega
  --But we know 3 doesn't divide 4.
  have hthreeNDivFour : ¬ (3 ∣ 4) := by omega
  --This gives us a contradiction.
  contradiction
  --Since 3 doesn't divide 4, it follows that eaither 4 * y + 1 % 3 = 1 or 2
  have hthreeModulo : (4 * y + 1) % 3 = 1 ∨ (4 * y + 1) % 3 = 2 := by
    omega
  --Now we do a case analysis.
  by_cases
  --Case 1 : (4 * y + 1) % 3 = 1
  hmoduloThreeEqOne : (4 * y + 1) % 3 = 1
  --Now it's easy to see that 3 ∣ 4 * y
  have hthreeDivFourY : 3 ∣ 4 * y := by omega
  --Since 3 and 4 are coprime, 3 must divide y.
  have hthreeDivY : 3 ∣ y := by omega
  --Now it follows that (4 * y + 1)^2 % 3 = 1
  have hmoduloThreeEqOne : (4 * y + 1)^2 % 3 = 1 := by
    rcases hthreeDivY with ⟨k, h3⟩
    calc
      _ = (16 * y^2 + 8 * y + 1) % 3 := by omega
      _ = (16 * (3 * k)^2 + 8 * (3 * k) + 1) % 3 := by rw [h3]
      _ = (144 * k^2 + 24 * k + 1) % 3 := by ring_nf
      _ = ((144 * k^2) % 3 + (24 * k) % 3 + 1 % 3) := by omega
      _ = 1 := by omega
  --Now it's easy to see that 3 * x^2 modulo 3 equals 2
  have hwhatever : (3 * x^2) % 3 = 2 := by omega
  --But since 3 divides 3 * x^2, it doesn't equal 2 modulo 3.
  have hwhatever' : (3 * x^2) % 3 ≠ 2 := by omega
  --Thus we have a contradiction.
  contradiction
  --Case 2: (4 * y + 1) % 3 = 1.
  have hmoduloThreeEqTwo : (4 * y + 1) % 3 = 2 := by tauto
  --Then it follows that 3 ∣ (4 * y - 1).
  have hthreeDivSubject : 3 ∣ (4 * y - 1) := by omega
  rcases hthreeDivSubject with ⟨k, hk⟩
  --Now it follows that 4 * y = 3 * k + 1.
  have hfourY : 4 * y = 3 * k + 1 := by linarith
  --Then it follows that (4 * y + 1)^2 % 3 = 1
  have hmoduloThreeEqOne : (4 * y + 1)^2 % 3 = 1 := by
    calc
      _ = (3 * k + 2)^2 % 3 := by rw [←hk]; ring_nf
      _ = (9 * k^2 + 12 * k + 4) % 3 := by ring_nf
      _ = (9 * k^2) % 3 + (12 * k) % 3 + 4 % 3 := by omega
      _ = 1 := by omega
  --Now it's easy to see that 3 * x^2 modulo 3 equals 2
  have hwhatever : (3 * x^2) % 3 = 2 := by omega
  --But since 3 divides 3 * x^2, it doesn't equal 2 modulo 3.
  have hwhatever' : (3 * x^2) % 3 ≠ 2 := by omega
  --Thus we have a contradiction.
  contradiction
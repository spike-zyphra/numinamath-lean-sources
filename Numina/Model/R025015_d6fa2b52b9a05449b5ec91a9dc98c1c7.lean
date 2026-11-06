import Mathlib

theorem algebra_302942 (a : Fin 10 → ℕ) (ha : ∀ i, 0 < a i)
    (hdist : ∀ i j, i ≠ j → a i ≠ a j)
    (h2 : a 1 = a 0 + a 4) (h3 : a 2 = a 1 + a 5)
    (h4 : a 3 = a 2 + a 6) (h6 : a 5 = a 4 + a 7)
    (h7 : a 6 = a 5 + a 8) (h9 : a 8 = a 7 + a 9) :
    a 3 ≥ 20 := by

  have h01 : a 0 ≥ 1 := by 
    linarith [ha 0]
  have h11 : a 1 ≥ 1 := by 
    linarith [ha 1]
  have h41 : a 4 ≥ 1 := by 
    linarith [ha 4]
  have h51 : a 5 ≥ 1 := by 
    linarith [ha 5]
  have h61 : a 6 ≥ 1 := by 
    linarith [ha 6]
  have h71 : a 7 ≥ 1 := by 
    linarith [ha 7]
  have h81 : a 8 ≥ 1 := by 
    linarith [ha 8]
  have h91 : a 9 ≥ 1 := by 
    linarith [ha 9]

  -- Transform hdist into concrete constraints
  have h01' : a 0 ≠ a 1 := hdist 0 1 (by simp)
  have h02 : a 0 ≠ a 2 := hdist 0 2 (by simp)
  have h03 : a 0 ≠ a 3 := hdist 0 3 (by simp)
  have h04 : a 0 ≠ a 4 := hdist 0 4 (by simp)
  have h05 : a 0 ≠ a 5 := hdist 0 5 (by simp)
  have h06 : a 0 ≠ a 6 := hdist 0 6 (by simp)
  have h07 : a 0 ≠ a 7 := hdist 0 7 (by simp)
  have h08 : a 0 ≠ a 8 := hdist 0 8 (by simp)
  have h09 : a 0 ≠ a 9 := hdist 0 9 (by simp)
  have h12 : a 1 ≠ a 2 := hdist 1 2 (by simp)
  have h13 : a 1 ≠ a 3 := hdist 1 3 (by simp)
  have h14 : a 1 ≠ a 4 := hdist 1 4 (by simp)
  have h15 : a 1 ≠ a 5 := hdist 1 5 (by simp)
  have h16 : a 1 ≠ a 6 := hdist 1 6 (by simp)
  have h17 : a 1 ≠ a 7 := hdist 1 7 (by simp)
  have h18 : a 1 ≠ a 8 := hdist 1 8 (by simp)
  have h19 : a 1 ≠ a 9 := hdist 1 9 (by simp)
  have h23 : a 2 ≠ a 3 := hdist 2 3 (by simp)
  have h24 : a 2 ≠ a 4 := hdist 2 4 (by simp)
  have h25 : a 2 ≠ a 5 := hdist 2 5 (by simp)
  have h26 : a 2 ≠ a 6 := hdist 2 6 (by simp)
  have h27 : a 2 ≠ a 7 := hdist 2 7 (by simp)
  have h28 : a 2 ≠ a 8 := hdist 2 8 (by simp)
  have h29 : a 2 ≠ a 9 := hdist 2 9 (by simp)
  have h34 : a 3 ≠ a 4 := hdist 3 4 (by simp)
  have h35 : a 3 ≠ a 5 := hdist 3 5 (by simp)
  have h36 : a 3 ≠ a 6 := hdist 3 6 (by simp)
  have h37 : a 3 ≠ a 7 := hdist 3 7 (by simp)
  have h38 : a 3 ≠ a 8 := hdist 3 8 (by simp)
  have h39 : a 3 ≠ a 9 := hdist 3 9 (by simp)
  have h45 : a 4 ≠ a 5 := hdist 4 5 (by simp)
  have h46 : a 4 ≠ a 6 := hdist 4 6 (by simp)
  have h47 : a 4 ≠ a 7 := hdist 4 7 (by simp)
  have h48 : a 4 ≠ a 8 := hdist 4 8 (by simp)
  have h49 : a 4 ≠ a 9 := hdist 4 9 (by simp)
  have h56 : a 5 ≠ a 6 := hdist 5 6 (by simp)
  have h57 : a 5 ≠ a 7 := hdist 5 7 (by simp)
  have h58 : a 5 ≠ a 8 := hdist 5 8 (by simp)
  have h59 : a 5 ≠ a 9 := hdist 5 9 (by simp)
  have h67 : a 6 ≠ a 7 := hdist 6 7 (by simp)
  have h68 : a 6 ≠ a 8 := hdist 6 8 (by simp)
  have h69 : a 6 ≠ a 9 := hdist 6 9 (by simp)
  have h78 : a 7 ≠ a 8 := hdist 7 8 (by simp)
  have h79 : a 7 ≠ a 9 := hdist 7 9 (by simp)
  have h89 : a 8 ≠ a 9 := hdist 8 9 (by simp)
  -- Try omega
  all_goals
  try omega
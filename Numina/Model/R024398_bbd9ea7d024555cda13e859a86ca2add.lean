import Mathlib

theorem number_theory_293131 (a : Fin 42 → ℕ) (ha : ∀ i j, i < j → a i > a j)
    (ha' : a 41 > 0) :
    ∑ i, a i ≥ 903 := by
  have h41 : a 41 ≥ 1 := by omega
  have h40 : a 40 ≥ 2 := by
    have h40 : a 40 > a 41 := by
      apply ha 40 41
      simp
    omega
  have h39 : a 39 ≥ 3 := by
    have h39 : a 39 > a 40 := by
      apply ha 39 40
      simp
    omega
  have h38 : a 38 ≥ 4 := by
    have h38 : a 38 > a 39 := by
      apply ha 38 39
      simp
    omega
  have h37 : a 37 ≥ 5 := by 
    have h37 : a 37 > a 38 := by 
      apply ha 37 38
      simp
    omega
  have h36 : a 36 ≥ 6 := by 
    have h36 : a 36 > a 37 := by 
      apply ha 36 37
      simp
    omega
  have h35 : a 35 ≥ 7 := by 
    have h35 : a 35 > a 36 := by 
      apply ha 35 36
      simp
    omega
  have h34 : a 34 ≥ 8 := by 
    have h34 : a 34 > a 35 := by 
      apply ha 34 35
      simp
    omega
  have h33 : a 33 ≥ 9 := by 
    have h33 : a 33 > a 34 := by 
      apply ha 33 34
      simp
    omega
  have h32 : a 32 ≥ 10 := by 
    have h32 : a 32 > a 33 := by 
      apply ha 32 33
      simp
    omega
  have h31 : a 31 ≥ 11 := by 
    have h31 : a 31 > a 32 := by 
      apply ha 31 32
      simp
    omega
  have h30 : a 30 ≥ 12 := by 
    have h30 : a 30 > a 31 := by 
      apply ha 30 31
      simp
    omega
  have h29 : a 29 ≥ 13 := by 
    have h29 : a 29 > a 30 := by 
      apply ha 29 30
      simp
    omega
  have h28 : a 28 ≥ 14 := by 
    have h28 : a 28 > a 29 := by 
      apply ha 28 29
      simp
    omega
  have h27 : a 27 ≥ 15 := by 
    have h27 : a 27 > a 28 := by 
      apply ha 27 28
      simp
    omega
  have h26 : a 26 ≥ 16 := by 
    have h26 : a 26 > a 27 := by 
      apply ha 26 27
      simp
    omega
  have h25 : a 25 ≥ 17 := by 
    have h25 : a 25 > a 26 := by 
      apply ha 25 26
      simp
    omega
  have h24 : a 24 ≥ 18 := by 
    have h24 : a 24 > a 25 := by 
      apply ha 24 25
      simp
    omega
  have h23 : a 23 ≥ 19 := by 
    have h23 : a 23 > a 24 := by 
      apply ha 23 24
      simp
    omega
  have h22 : a 22 ≥ 20 := by 
    have h22 : a 22 > a 23 := by 
      apply ha 22 23
      simp
    omega
  have h21 : a 21 ≥ 21 := by 
    have h21 : a 21 > a 22 := by 
      apply ha 21 22
      simp
    omega
  have h20 : a 20 ≥ 22 := by 
    have h20 : a 20 > a 21 := by 
      apply ha 20 21
      simp
    omega
  have h19 : a 19 ≥ 23 := by 
    have h19 : a 19 > a 20 := by 
      apply ha 19 20
      simp
    omega
  have h18 : a 18 ≥ 24 := by 
    have  h18 : a 18 > a 19 := by 
      apply ha 18 19
      simp
    omega
  have h17 : a 17 ≥ 25 := by 
    have h17 : a 17 > a 18 := by 
      apply  ha 17 18
      simp
    omega
  have h16 : a 16 ≥ 26 := by 
    have h16 : a 16 > a 17 := by 
      apply ha 16 17
      simp
    omega
  have h15 : a 15 ≥ 27 := by 
    have h15 : a 15 > a 16 := by 
      apply  ha 15 16
      simp
    omega
  have h14 : a 14 ≥ 28 := by 
    have h14 : a 14 > a 15 := by 
      apply  ha 14 15
      simp
    omega
  have h13 : a 13 ≥ 29 := by 
    have h13 : a 13 > a 14 := by 
      apply  ha 13 14
      simp
    omega
  have h12 : a 12 ≥ 30 := by 
    have  h12 : a 12 > a 13 := by 
      apply  ha 12 13
      simp
    omega
  have h11 : a 11 ≥ 31 := by 
    have  h11 : a 11 > a 12 := by 
      apply  ha 11 12
      simp
    omega
  have h10 : a 10 ≥ 32 := by 
    have h10 : a 10 > a 11 := by 
      apply ha 10 11
      simp
    omega
  have h9 : a 9 ≥ 33 := by 
    have h9 : a 9 > a 10 := by 
      apply  ha 9 10
      simp
    omega
  have h8 : a 8 ≥ 34 := by 
    have  h8 : a 8 > a 9 := by 
      apply  ha 8 9
      simp
    omega
  have h7 : a 7 ≥ 35 := by 
    have  h7 : a 7 > a 8 := by 
      apply  ha 7 8
      simp
    omega
  have h6 : a 6 ≥ 36 := by 
    have  h6 : a 6 > a 7 := by 
      apply  ha 6 7
      simp
    omega
  have h5 : a 5 ≥ 37 := by 
    have  h5 : a 5 > a 6 := by 
      apply  ha 5 6
      simp
    omega
  have h4 : a 4 ≥ 38 := by 
    have  h4 : a 4 > a 5 := by 
      apply  ha 4 5
      simp
    omega
  have h3 : a 3 ≥ 39 := by 
    have  h3 : a 3 > a 4 := by 
      apply  ha 3 4
      simp
    omega
  have h2 : a 2 ≥ 40 := by 
    have  h2 : a 2 > a 3 := by 
      apply  ha 2 3
      simp
    omega
  have h1 : a 1 ≥ 41 := by 
    have  h1 : a 1 > a 2 := by 
      apply  ha 1 2
      simp
    omega
  have h0 : a 0 ≥ 42 := by 
    have  h0 : a 0 > a 1 := by 
      apply  ha 0 1
      simp
    omega
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at *
  <;> linarith
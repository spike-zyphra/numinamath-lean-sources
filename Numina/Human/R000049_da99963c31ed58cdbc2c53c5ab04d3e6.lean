
import Mathlib

-- Initial Number of Pencils
def initial_pencils : Nat := 2015

-- Loss of Pencils
def lost_pencils : Nat := 5

-- Gain of Pencils
def gained_pencils : Nat := 50

-- Finial pencils
def final_pencils : Nat :=
  initial_pencils - lost_pencils + gained_pencils

/-- The students in class 5A had a total of 2015 pencils. One of them lost a box containing five pencils and replaced it with a box containing 50 pencils. How many pencils do the students in class 5A have now?-/
theorem Arithmetic_4182 : final_pencils = 2060 := by
  unfold final_pencils
  simp [initial_pencils, lost_pencils, gained_pencils]


#eval final_pencils
-- 输出最终铅笔数量

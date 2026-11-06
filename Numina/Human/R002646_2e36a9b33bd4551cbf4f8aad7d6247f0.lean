import Mathlib

/- The bar graph shows the results of a survey on color preferences.  What percent preferred blue?
(A) 20%(B) 24%(C) 30%(D) 36%(E) 42% -/
theorem other_97727 (total_people : ℕ) (h₁ : total_people = 250) 
(blue_preferred : ℕ) (h₂ : blue_preferred = 60) : 
(blue_preferred / total_people : ℚ) * 100 = 24 := by rw[h₁, h₂]; ring
--from the graph we know both that the total number of people is 250 and the people that prefer blue are 60. Then we compute the percentage the usual way.
import Mathlib
import Mathlib.Tactic.NormNum

/--
At an elementary school, the students in third grade, fourth grade, and fifth grade
run an average of 12, 15, and 10 minutes per day, respectively. There are twice as
many third graders as fourth graders, and twice as many fourth graders as fifth
graders. What is the average number of minutes run per day by these students?

(A) 12  
(B) 37/3  
(C) 88/7  
(D) 13  
(E) 14
-/

theorem algebra_93068 :
  ∀ c : ℕ, 0 < c →
    (12 * (4 * c) + 15 * (2 * c) + 10 * c : ℝ) / (4 * c + 2 * c + c) = 88 / 7 :=
fun c hc => by
  calc
    -- Basically, to compute the average number of minutes run per day by these students, we use the definition of average which based on the data given in the statement is equivalent to
    (12 * (4*c) + 15 * (2*c) + 10 * c : ℝ) / (4*c + 2*c + c)
      = (48*c + 30*c + 10*c : ℝ) / (7*c) := by ring
    _ = (88*c : ℝ) / (7*c) := by ring
    -- Here, canceling out c since hc>0 (c≠0)
    _ = 88 / 7 := by
      field_simp [hc]
      -- Finally, to show "88 * ↑c * 7 = 88 * (7 * ↑c)", we just use commutativity via ring
      ring
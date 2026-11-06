import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/--
Mr. Patrick teaches math to 15 students. He was grading tests and found that
when he graded everyone's test except Payton's, the class average was 80. After
he graded Payton's test, the average became 81. What was Payton's score on the
test?

(A) 81   (B) 85   (C) 91   (D) 94   (E) 95
-/
theorem algebra_95282 (total_students : Int) (h : total_students = 15)
    (_payton_score : Int)
    (h1 : (total_students - 1) * 80 + _payton_score = total_students * 81) :
    _payton_score = 95 := by
  calc
    _payton_score
   -- First, we convert `_payton_score` into the form (total_studens - 1)*80 + _payton_score - (total_students - 1)*80
      = (total_students - 1) * 80 + _payton_score - (total_students - 1) * 80 := by
        ring 
   -- Now, we rewrite using `h1` we get to reduce the equation
    _ = total_students * 81 - (total_students - 1) * 80 := by
      rw [h1]
   -- Then, we substitute total_students = 15 into the above equation and then just operate arithmetically
    _ = 15 * 81 - (15 - 1) * 80 := by
      rw [h]
    _ = 1215 - 1120 := by
      norm_num
    _ = 95 := by norm_num
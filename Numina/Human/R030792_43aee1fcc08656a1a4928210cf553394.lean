import Mathlib

/- Last academic year Yolanda and Zelda took different courses that did not necessarily
administer the same number of quizzes during each of the two semesters. Yolanda's average
on all the quizzes she took during the first semester was 3 points higher than Zelda's average
on all the quizzes she took during the first semester. Yolanda's average on all the quizzes
she took during the second semester was 18 points higher than her average for the first semester and was again
3 points higher than Zelda's average on all the quizzes Zelda took during her second semester.
Which one of the following statements cannot possibly be true?
(A) Yolanda's quiz average for the academic year was 22 points higher than Zelda's.
(B) Zelda's quiz average for the academic year was higher than Yolanda's.
(C) Yolanda's quiz average for the academic year was 3 points higher than Zelda's.
(D) Zelda's quiz average for the academic year equaled Yolanda's.
(E) If Zelda had scored 3 points higher on each quiz she took, then she would have had the same average for the academic year as Yolanda. -/
theorem algebra_95870 (z1 z2 y1 y2:ℝ)
(h1 : (z1 + 3) = y1)
(h2 : (y1 + 18) = y2)
(h3: z2 + 3 = y2)
(h4: z1 + 18 = z2)
: y1 + y2 ≠ z1 + z2 + 22 := by
  -- gain hypothesis by reducing inequality
  intro abc
  -- turn equations so they are of the form x = _
  symm at h2 h1 h3 h4
  -- substitute variables with known hypothesis
  rw [h2, h4, h1] at abc
  -- calculate sum
  ring_nf at abc
  -- reduce both sides and cancle-out parts that equal zero
  apply congr_arg (fun f => f - z1 * 2) at abc
  ring_nf at abc
  norm_num at abc
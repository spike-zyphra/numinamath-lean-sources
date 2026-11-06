import Mathlib.Tactic

/-
PROBLEM:
Postman Pete has a pedometer to count his steps. The pedometer records up to $99999$ steps, then flips over to $00000$ on the next step. Pete plans to determine his mileage for a year. On January $1$ Pete sets the pedometer to $00000$. During the year, the pedometer flips from $99999$ to $00000$ forty-four times. On December $31$ the pedometer reads $50000$. Pete takes $1800$ steps per mile. Which of the following is closest to the number of miles Pete walked during the year?
$\textbf{(A)}\ 2500 \qquad \textbf{(B)}\ 3000 \qquad \textbf{(C)}\ 3500 \qquad \textbf{(D)}\ 4000 \qquad \textbf{(E)}\ 4500$
-/

theorem num_theory_1198
  (flips r_sc t_sc : ℕ)
  (miles : ℝ)
  (total_flips : flips = 44)
  (total_step_count : t_sc = flips * 100000 + r_sc)
  (remaining_step_count : r_sc = 50000)
  (total_miles : miles = t_sc / 1800 ) :
  miles = 22250 / 9 := by
    rw [remaining_step_count, total_flips] at total_step_count
    norm_num at total_step_count
    rw [total_step_count] at total_miles
    norm_num at total_miles
    aesop
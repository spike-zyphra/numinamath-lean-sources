import Mathlib

-- The sum of the digits of the time 19 minutes ago is two less than the sum of the digits of the time right now. Find the sum of the digits of the time in 19 minutes. (Here, we use a standard 12-hour clock of the form hh:mm.)
namespace number_theory_610339

def hour_digits h :=
  let h' := if h = 0 then 12 else h
  Nat.digits 10 h'
def minute_digits m :=
  Nat.digits 10 m
def sum_of_digits (time_in_min : Fin (12 * 60)) :=
  let t := time_in_min.val
  let h := t / 60
  let m := t % 60
  let h_digits := hour_digits h
  let m_digits := minute_digits m
  h_digits.sum + m_digits.sum

theorem number_theory_610339 : (time_in_min : Fin (12 * 60)) →
    sum_of_digits (time_in_min - 19) = sum_of_digits time_in_min - 2 →
    sum_of_digits (time_in_min + 19) = 11 := by
  native_decide

end number_theory_610339
open number_theory_610339

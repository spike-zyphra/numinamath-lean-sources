import Mathlib

open List

def sol_4090 := ((Ico 100 126).append (Ico 200 226)).map
  fun n => (if n % 10 = 1 then 1 else 0) +
    (if n % 100 / 10 = 1 then 1 else 0) +
    (if n % 1000 / 100 = 1 then 1 else 0)

/- The landlord of an apartment building needs to purchase enough digits to label all of the apartments from 100 through 125 on the first floor and 200 through 225 on the second floor. The digits can only be purchased in a package that contains one of each digit 0 through 9. How many packages must the landlord purchase?-/
theorem prealgebra_4090 : sol_4090.sum = 52 := by
  -- verify by computation
  native_decide

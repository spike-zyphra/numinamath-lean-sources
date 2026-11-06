import Mathlib

/- An astronomer has observed that a satellite orbits the Earth in a period that is an exact multiple of 1 hour and is less than 24 hours. The astronomer notes that the satellite completes 11 orbits during a time interval that starts when a 24-hour clock reads 0 hours and ends when the clock reads 17 hours. The task is to determine the orbital period of the satellite.-/
theorem number_theory_4687 (T : Fin 24) (h : 11*T%24=0) (h2 : T>0) :
    T=19 := by
  fin_cases T
  simp at h2
  any_goals simp at h

import Mathlib

theorem algebra_301131 (a b c : ℕ) (_ : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : 1 < a) (h2 : a < b) (h3 : b < c) (h4 : a + b + c = 111) (h5 : b^2 = a * c) :
    b = 36 := by
  have h6 : c = 111 - a - b := by
    omega
  rw [h6] at h5
  have h7 : a ≤ 36 := by
    nlinarith [h2, h3, h4, h1]
  have h8 : b ≤ 55 := by
    nlinarith [h2, h3, h4, h1]
  interval_cases a <;> try {
    interval_cases b <;> omega
  }
  <;> try { 
      all_goals 
      omega
  }
  <;> try { 
    all_goals 
    nlinarith
    all_goals
    try { 
      omega
    }
  }
  <;> try { 
    all_goals 
    nlinarith
    all_goals
    try { 
      omega
    }
  }
  all_goals
  try {
    nlinarith
  }
  all_goals
  try { 
    omega
  }
  all_goals
  try { 
    nlinarith
    all_goals
    try { 
      omega
    }
  }
  all_goals
  try { 
    nlinarith
  }
  all_goals
  try { 
    omega
  }
  all_goals
  try { 
    nlinarith
  }
  all_goals
  try { 
    omega
  }
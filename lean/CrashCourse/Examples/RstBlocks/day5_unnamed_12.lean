namespace vmcsp
  def tau := "TAU on M-Th from 1-3"
  #eval tau
end vmcsp

def tau := "no TAU on F"
#eval tau
#eval vmcsp.tau

open vmcsp

-- #eval tau  -- error: `tau` is now ambiguous between `_root_.tau` and `vmcsp.tau`
#eval vmcsp.tau
import Commitments


def main : IO Unit := do
  IO.println "Hello, world!"

  let x' ← commit q' t k  
  pure (x')

  let x' ← commit q' t k  
  pure (x').2



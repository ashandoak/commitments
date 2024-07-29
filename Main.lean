import Commitments


variable {G : Type} [Group G] [Fintype G] 
variable {g : G}

def main : IO Unit := do
  IO.println "Hello, world!"

  let key := ElGamal.keygen
  let h := key.1

  let q := 17
  let m := "test"
  let x' ← ElGamal.commit h _  




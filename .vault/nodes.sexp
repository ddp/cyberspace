;; Library of Cyberspace - Node Fleet
;; Confederation founding nodes

(nodes
  (node
    (name "fluffy")
    (role master)
    (hardware "Mac Studio M2 Ultra")
    (cpu "M2 Ultra")
    (memory "192GB")
    (storage "8TB")
    (notes "Origin node, primary vault"))

  (node
    (name "om")
    (role full)
    (hardware "14\" MacBook Pro")
    (cpu "M4 Max")
    (memory "128GB")
    (storage "4TB")
    (notes "Mobile powerhouse"))

  (node
    (name "lambda")
    (role witness)
    (hardware "MacBook Pro")
    (cpu "1.2GHz Quad-Core Intel Core i7")
    (memory "16GB")
    (storage "1TB")
    (notes "Legacy Intel node"))

  (node
    (name "starlight")
    (role full)
    (hardware "15\" MacBook Air")
    (cpu "M4 10-core")
    (memory "32GB")
    (storage "2TB")
    (status incoming)
    (notes "Starlight color, ordered Jan 2025")))

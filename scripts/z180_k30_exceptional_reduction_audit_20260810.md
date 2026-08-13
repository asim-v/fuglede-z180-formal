# Auditoría exacta de la reducción excepcional K30

Fecha: 2026-08-10. Alcance: solo la reducción desde la conclusión estructural
`L = R + 30 Z_180` hasta un mosaico de `A`; no se atribuye al certificado de
enumeración ninguno de los lemas estructurales que este declara externos.

## Hipótesis y notación

Sean `A,L ⊂ Z_180`, `|A|=|L|=30`, con `L` espectro de `A`. Se usa la
convención positiva del repositorio

`fourierSum A (l1-l2) = sum_(a in A) zeta_180^(a(l1-l2))`.

Sea `H = 30 Z_180 = {30t : t in Z_6}` y supóngase
`L = pi^(-1)(R) = R + H`, donde `pi : Z_180 -> Z_30` y `|R|=5`.
Para `c in Z_6`, la aplicación

`iota_c : Z_30 -> {a in Z_180 : a mod 6 = c},  d |-> c+6d`

es biyectiva. Defínase `D_c = iota_c^(-1)(A)` y `n_c=|D_c|`.

## Las tres identidades exactas

1. Balance de las seis clases. Fijado `r in R`, para `t=1,...,5` los dos
   elementos `r+30t` y `r` de `L` son distintos. La ortogonalidad da

   `0 = sum_(a in A) zeta_180^(30ta) = sum_(c in Z_6) n_c zeta_6^(ct)`.

   Junto con `sum_c n_c=30`, la inversión de la DFT de orden seis da
   `n_c=5` para todo `c`.

2. Descenso acoplado, no marginal. Sean `r != s` en `R`, sea
   `delta = r_tilde-s_tilde` para lifts cualesquiera, y sea `t in Z_6`.
   Los elementos `r_tilde+30t` y `s_tilde` son distintos, y

   `0 = sum_(a in A) zeta_180^(a(delta+30t))`

   `  = sum_(c in Z_6) zeta_6^(ct) zeta_180^(c delta)
       [sum_(d in D_c) zeta_30^(d delta)]`.

   Al invertir de nuevo la DFT de orden seis, cada corchete es cero. Como
   `delta mod 30 = r-s`, esto prueba exactamente

   `CyclotomicSpectrum 30 D_c R`

   para todo `c`: `D_c` es no vacío, `|D_c|=|R|=5`, y su máscara se anula
   en cada diferencia no nula de `R`. Cambiar los lifts solo permuta `t`,
   por lo que no introduce una condición adicional ni un error de carry.

3. Transversal y mosaico. El teorema
   `z30_k5_projection5_injOn_of_spectral`, aplicado con lado conjunto
   `D_c` y lado espectro `R`, hace a cada `D_c` transversal módulo cinco.
   Si `a=c+6d` y `a'=c'+6d'` tienen el mismo residuo módulo treinta,
   entonces primero `c=c'` módulo seis y después `d=d'` módulo cinco.
   La inyectividad en `D_c` fuerza `d=d'` en `Z_30`, y por tanto `a=a'`
   en `Z_180`. La proyección `A -> Z_30` es inyectiva y, por cardinalidad,
   biyectiva. En consecuencia la suma

   `A x H -> Z_180, (a,h) |-> a+h`

   es biyectiva: `Tiles A H`.

## Chequeo de orientación del certificado excepcional

En `audit_z180_k30_exceptional_exact.mjs`, `gram(U,V)` usa

`sum_(u in U) zeta_36^(u (V_column-V_row))`.

Esto es el Gram de columnas `M(U,V)^* M(U,V)`. En la matriz de Fourier
global las filas son los bloques `A_c` y las columnas los bloques `L_q`;
por tanto, en esa rutina `U=A_c` y `V=L_q`. `gramStarAudit` suma los cinco
Grams obtenidos al variar `c`, manteniendo `V=L_q` fijo, y los compara con
`30 I_6`. El único sobreviviente `V` es la órbita afín de
`6 Z_36 = {0,6,12,18,24,30}`. Una unidad de `Z_36` preserva este subgrupo,
así que su órbita afín consta exactamente de sus cosets. Por ello cada
`L_q`, no cada `A_c`, es un coset de `6 Z_36`; al recombinar por CRT se
obtiene precisamente `L=R+30 Z_180`.

Resultado de la auditoría: orientación de lados correcta, signo
`l1-l2` correcto y ningún hueco desde `L=R+H` hasta `Tiles A H`.

## Frontera que sigue siendo externa

El certificado de enumeración no prueba: (i) la reducción proyectiva de
matrices unimodulares de rango dos, (ii) la identificación de clases
proyectivas con clases residuales, (iii) la dicotomía bloque común/rango dos,
ni (iv) la propagación de un bloque excepcional a los 25 bloques. Esos pasos
siguen siendo premisas anteriores a este informe.

## Fuentes auditadas (SHA-256)

- `scripts/audit_z180_k30_exceptional_exact.mjs`:
  `39B8BB28B8B0DF30D69C67FC035277DDAB77D4FBB45681DF6BB940E1A24CF02B`
- `scripts/z180_k30_exceptional_exact.certificate.json`:
  `ABBFF997C44A6292880B9C89FACF2D3C57E1126A6BFF170BB7695F2DEC6BA352`
- `fuglede_lean/Fuglede/SpectralFourier.lean`:
  `E9F38AF40BE2F48083ACA11E6895B1C2AB739BB8D29CAD7B4734DBE3A2C9F084`
- `fuglede_lean/Fuglede/Z30K5InflationBridge.lean`:
  `B22DEA6B0FD4C11040D4AA81AA859B2BF4C83A31272E931EE199308942610353`

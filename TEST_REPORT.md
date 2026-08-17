# Informe de reprueba — ConformalLagrangianSATSolver (strict 3-SAT)

Fecha: 2026-08-17

## Resultado

Comando:

```bash
python -m unittest -v test_sat_solver.py
```

Salida resumida:

```text
Ran 24 tests in 0.817s
OK
```

- **24/24 pruebas pasaron.**
- Sin fallos ni fallos esperados.
- Se añadieron aserciones para rechazar `bool` en el generador y para exigir enteros exactos en `verify_solution`.

También se ejecutó directamente el programa:

```text
Base Result: [1, 0, 0, 0, 0, 0] | Validated: True
Dense Result: [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0] | Validated: True
```

## Comprobaciones cubiertas

- Tipos y rangos de `num_vars`, `max_flips` y `gauge_step`.
- Tipo de `clauses` y de cada cláusula.
- Cláusulas con exactamente tres literales.
- Rechazo de literales cero, fuera de rango, no enteros y booleanos.
- Rechazo de variables repetidas, incluso con polaridades opuestas como `[1, -1, 2]`.
- Semántica de literales y conteo de satisfacción.
- Inicialización del estado incremental.
- `hypothetical_flip_delta` contra recálculo completo en 100 casos pseudoaleatorios reproducibles.
- `apply_flip` contra recálculo completo después de 250 flips.
- Verificación de longitud, `None` y valores fuera de `{0, 1}`.
- Asignación inicial de ceros.
- Desempate por el menor índice.
- Determinismo en cinco ejecuciones idénticas.
- Límites de cero flips y fórmula vacía.
- Fórmula estricta conocida como UNSAT.
- Las 256 subfórmulas canónicas generadas con las ocho cláusulas posibles sobre tres variables.
- 120 fórmulas pequeñas contrastadas con un solver exhaustivo de referencia.
- Reproducibilidad del generador y validez de la solución plantada.
- Confirmación de que el generador no modifica el estado del RNG global.
- Benchmark `n=20, m=80, seed=2026`.
- Ejecución con `gauge_step` igual a 1, 2 y 7.

## Estrés adicional

Se generaron 100 instancias plantadas con `n=20`, `m=85`, semillas 0–99 y `max_flips=10_000`:

```text
100/100 resueltas y verificadas
Tiempo total: 0.1802 s
```

## Conclusión

La corrección de `verify_solution`, la validación de 3-SAT estricto y el uso de un RNG local funcionan según lo esperado. No se detectaron errores funcionales en la suite actual.

Esto sigue siendo evidencia empírica y no demuestra completitud: `None` significa únicamente que no se encontró una solución dentro de `max_flips`.

## Correcciones finales de rigurosidad

1. `generate_satisfiable_bench` ahora rechaza explícitamente `bool` tanto para `n_vars` como para `n_clauses`.
2. `verify_solution` exige que cada entrada tenga tipo exacto `int` y valor 0 o 1; rechaza `float`, `bool` y subclases de `int`.

Ambas correcciones están cubiertas por pruebas de regresión y funcionan correctamente.

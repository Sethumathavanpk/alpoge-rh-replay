"""Check and measure shared lemmas against source-hashed declarations from the archive."""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from scan import ROOT, indexed_sources, declarations

HERE = Path(__file__).resolve().parent
LEAN_COMMIT = '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
LIBRARIES = {
    'ReplayTopology': (
        'continuous_unitsHom',
        'totallyDisconnected_quotient',
        'continuous_charpoly_coeff',
    ),
    'ReplayAlgebra': (
        'specMap_ofHom_comp',
        'cardQuot_under_eq_pow_inertiaDeg',
        'not_isTotallyReal_and_isTotallyComplex',
        'padicAlgCl_isIntegral_iff_norm_le_one',
        'isLocalHom_of_isIntegral',
    ),
}
WRAPPER_TASKS = {'M144183', 'M172691'}

# Each entry identifies the exact text (statement and proof), the shared lemma group,
# the replacement proof term, whether the consumer statement mentions an archive abbreviation
# (`spMap` or `normV`), and the source modules found by scan.py --match.
CASES = {
    '34271c25953e82f6977370f84a264df5bc8ad183a5f95a8e230f21bc4be9f670': (
        'specMap_ofHom_comp', 'ReplayAlgebra.specMap_ofHom_comp f g', True,
        'M002912 M012786 M013117 M014298 M024847 M025845 M029787 M032194 M037630 M040488 '
        'M046038 M050016 M050017 M052056 M052533 M052563 M052565 M054760 M069696 M075703 '
        'M077426 M077638 M082053 M084760 M085259 M085303 M085610 M085741 M091233 M110308 '
        'M110319 M130333 M140422'),
    'fd75d6b9f2b9fc3699439fa3b3ea292f90f8885409ca497911de151ebb610149': (
        'specMap_ofHom_comp', '(ReplayAlgebra.specMap_ofHom_comp f g).symm', True,
        'M003372 M006593 M006945 M013265 M013611 M015851 M015855 M015969 M017847 M028894 '
        'M040341 M047824 M052573 M053220 M054185 M082736 M099865 M110231 M130257 M130301 '
        'M131923'),
    'eda0620c639c59e3f6e40925c97726c03a73c86684782e725f94ac5ac40264db': (
        'specMap_ofHom_comp', '(ReplayAlgebra.specMap_ofHom_comp f g).symm', True,
        'M017805 M025167 M028730 M029749 M077946 M081605 M100087 M110080 M110086 M110121 '
        'M173382'),
    '29905a26a348ec0d7c5c03d9db696235bf12097f17db7dd9edcbbda543795a2d': (
        'specMap_ofHom_comp', 'ReplayAlgebra.specMap_ofHom_comp f g', True,
        'M003622 M033540 M033569 M039944 M044540 M052029 M078943 M099657 M132269 M150382'),
    'd393a9b9374acc508ece03d7fee06b9bd2356c732fed8e72eda34761128230d2': (
        'specMap_ofHom_comp', 'ReplayAlgebra.specMap_ofHom_comp g f', True,
        'M006583 M006779 M007140 M007333 M051963 M060797 M064360 M083656 M099536'),
    'a11d5d73353c0057599dcc0479a75be33f17535b6bbe102a0e5c60562ca6cbc0': (
        'cardQuot_under_eq_pow_inertiaDeg', 'ReplayAlgebra.cardQuot_under_eq_pow_inertiaDeg K w', True,
        'M062774 M101975 M102029 M102068 M102069 M102265 M102273 M102379 M103380 M103381 '
        'M103391 M103403 M103420 M104178 M104974 M105067 M105069 M105081 M106614 M106661 '
        'M106684 M106824 M106995 M107068 M111777 M171275 M171321'),
    'b22f16de291d4844b697b2d4d3658ff78484851da81860c87effa4c28ff8a877': (
        'continuous_unitsHom', 'ReplayTopology.continuous_unitsHom f h', False,
        'M061176 M102348 M103013 M104155 M104175 M104194 M104195 M104350 M104351 M104984 '
        'M105041 M105077 M105078 M105715 M105987 M106690 M106694 M108432 M171108'),
    '3a85de910ca7ee70763c329e104f0e728010b921be90cf8d76a4e2541280444a': (
        'not_isTotallyReal_and_isTotallyComplex',
        "ReplayAlgebra.not_isTotallyReal_and_isTotallyComplex h h'", False,
        'M101968 M103446 M105061 M105067 M105075 M106651 M106661 M110968 M111468 M111473 '
        'M111587 M113132 M137230 M170999 M171003'),
    '6908455f17486d5184e88449ae58304e52d0bf55948f9ee9989a1bbf7e3a8f6a': (
        'totallyDisconnected_quotient', 'ReplayTopology.totallyDisconnected_quotient N hN', False,
        'M103041 M105902 M105903 M105904 M106665 M106666 M106667 M106913 M107059 '
        'M108306 M108608 M108635 M108656 M109071'),
    'dcfcbb1cc29edfb0b14f225589fa578d39fa77a23fa928dfafc0e6ae356f520c': (
        'continuous_charpoly_coeff', 'ReplayTopology.continuous_charpoly_coeff i', False,
        'M018532 M018573 M071680 M087066 M094014 M101722 M101992 M103922 M104974 M105067 '
        'M106661 M106954 M141687 M171293'),
    '69cf43c3647f8beb153fe01e3cfe355b6bfea9baed22ab22fa8e0dffc74ce72c': (
        'padicAlgCl_isIntegral_iff_norm_le_one',
        'ReplayAlgebra.padicAlgCl_isIntegral_iff_norm_le_one x', False,
        'M101497 M103902 M103989 M104010 M106930 M107631 M107632 M108269 M108336 M108691 '
        'M108890 M109256'),
    'bbf7ecd88deb2e088d7d122bc93d909378befff9ce5a554dc7b5e733ab8315bf': (
        'isLocalHom_of_isIntegral', 'ReplayAlgebra.isLocalHom_of_isIntegral f', False,
        'M103047 M105900 M105905 M105982 M105989 M106573 M106668 M108438 M108453'),
}


def source_cases(project):
    expected = {(task, key) for key, (_, _, _, tasks) in CASES.items() for task in tasks.split()}
    cases = []
    seen_names = Counter()
    for row, data in indexed_sources(project, {task for task, _ in expected}):
        for key, match, block in declarations(data):
            ident = (row['id'], key.hex())
            if ident not in expected:
                continue
            expected.remove(ident)
            lemma, term, needs_wrappers, _ = CASES[ident[1]]
            base_name = f"{ident[0]}.{match[1].decode()}"
            seen_names[base_name] += 1
            decl_name = base_name if seen_names[base_name] == 1 else f"{base_name}_{seen_names[base_name]}"
            cases.append((lemma, term, needs_wrappers, decl_name, block.decode('utf-8')))
    if expected:
        raise ValueError(f'Missing pinned declarations: {sorted(expected)}')
    return sorted(cases)


def compiler_environment(project, work):
    summary = json.loads((ROOT / 'tracker/summary.json').read_text(encoding='utf-8'))
    toolchain = (project / 'lean-toolchain').read_text(encoding='utf-8').strip()
    version = subprocess.check_output(['lean', '--version'], text=True).strip()
    if (toolchain != 'leanprover/lean4:v' + summary['lean'] or LEAN_COMMIT not in version
            or f"version {summary['lean']}," not in version):
        raise ValueError(f'Unexpected compiler: {version} ({toolchain})')
    manifest = json.loads((project / 'lake-manifest.json').read_text(encoding='utf-8'))
    packages = project / manifest['packagesDir']
    pins = [p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib']
    actual = subprocess.check_output(['git', '-C', packages / 'mathlib', 'rev-parse', 'HEAD'],
                                     text=True).strip()
    if pins != [actual] or actual != summary['mathlib_commit']:
        raise ValueError(f'Unexpected Mathlib revision: {actual}')
    libraries = [packages / p['name'] / '.lake/build/lib/lean' for p in manifest['packages']]
    return version, actual, {**os.environ, 'LEAN_PATH': os.pathsep.join(map(str, [work, *libraries]))}


def compile_file(work, env, rel_stem, save=False, warning_as_error=True):
    cmd = ['lean', '-j1', '-DElab.async=false', '-DautoImplicit=false',
           '-DrelaxedAutoImplicit=false', '-DmaxSynthPendingDepth=3', '-DmaxHeartbeats=4000000',
           f'-DwarningAsError={"true" if warning_as_error else "false"}', '--tstack=400000']
    if save:
        cmd.extend(['-o', rel_stem + '.olean'])
    run = subprocess.run([*cmd, rel_stem + '.lean'], env=env, cwd=work, text=True,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if run.returncode:
        raise RuntimeError(f"{rel_stem} failed:\n{run.stdout}")
    return [int(n) for n in re.findall(r'\bUsed (\d+) heartbeats,', run.stdout)]


def audit(names):
    constants = ', '.join('`' + name for name in names)
    return f'''
open Lean in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for decl in #[{constants}] do
    for ax in ← collectAxioms decl do
      unless allowed.contains ax do throwError m!"Unexpected axiom {{ax}} in {{decl}}"
'''


def prepare_wrappers(project, work, env):
    wrapper_modules = []
    for row, data in indexed_sources(project, WRAPPER_TASKS):
        rel_stem = row['module'].replace('.', '/')
        dest = work / (rel_stem + '.lean')
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        compile_file(work, env, rel_stem, save=True, warning_as_error=False)
        wrapper_modules.append(row['module'])
    if len(wrapper_modules) != len(WRAPPER_TASKS):
        raise ValueError('Missing wrapper modules')
    return sorted(wrapper_modules)


def check(project, work):
    cases = source_cases(project)
    version, pin, env = compiler_environment(project, work)

    library_costs = {}
    all_shared_decls = []
    for lib_name, decl_names in LIBRARIES.items():
        library = HERE / f'{lib_name}.lean'
        shutil.copyfile(library, work / library.name)
        compile_file(work, env, lib_name, save=True)
        subprocess.run(['leanchecker', lib_name], cwd=work, env=env, check=True)
        source = library.read_text(encoding='utf-8')
        source = 'import Mathlib.Util.CountHeartbeats\n' + source.replace('\n/--', '\n#count_heartbeats in\n/--')
        cost_stem = f'{lib_name}Cost'
        (work / (cost_stem + '.lean')).write_text(source, encoding='utf-8')
        costs = compile_file(work, env, cost_stem)
        if len(costs) != len(decl_names):
            raise ValueError(f'Missing {lib_name} heartbeat measurements ({len(costs)} != {len(decl_names)})')
        for dname, cost in zip(decl_names, costs):
            library_costs[dname] = cost
            all_shared_decls.append(f'{lib_name}.{dname}')

    wrapper_modules = prepare_wrappers(project, work, env)

    pure_cases = [c for c in cases if not c[2]]
    wrapped_cases = [c for c in cases if c[2]]

    measurements = {'Original': Counter(), 'Shared': Counter()}
    for mode in ('Original', 'Shared'):
        for batch_label, batch_cases, use_wrappers in (
            ('Pure', pure_cases, False),
            ('Wrapped', wrapped_cases, True),
        ):
            lines = ['import ReplayTopology', 'import ReplayAlgebra']
            if use_wrappers:
                for wmod in wrapper_modules:
                    lines.append(f'import {wmod}')
            lines.extend([
                'import Mathlib.Util.CountHeartbeats',
                'import Lean.Util.CollectAxioms',
                'open NumberField Polynomial',
                'open scoped Padic',
            ])
            if use_wrappers:
                lines.extend([
                    'open AlgebraicGeometry CategoryTheory IsDedekindDomain',
                    'open Formalism.ConjugateSelfDual (normV)',
                    'open ReciprocityTheory.ChartRestriction.G.Geo.Tor (spMap)',
                ])
            names = []
            for lemma, term, _, name, block in batch_cases:
                if mode == 'Shared':
                    statement, _, _ = block.partition(':= by')
                    block = f'{statement}:= {term}'
                lines.extend(['#count_heartbeats in', f'theorem {name} {block}'])
                names.append(name)
            lines.append(audit(names + (all_shared_decls if not use_wrappers else [])))
            stem = f'{mode}{batch_label}'
            (work / (stem + '.lean')).write_text('\n\n'.join(lines), encoding='utf-8')
            beats = compile_file(work, env, stem, warning_as_error=(mode == 'Shared' and not use_wrappers))
            if len(beats) != len(batch_cases):
                raise ValueError(f'Missing {stem} heartbeat measurements ({len(beats)} != {len(batch_cases)})')
            for (lemma, _, _, _, _), n in zip(batch_cases, beats):
                measurements[mode][lemma] += n

    return dict(
        compiler=version,
        mathlib=pin,
        kernel_replayed=list(LIBRARIES),
        checked=dict(Counter(c[0] for c in cases)),
        heartbeats={k: dict(v) for k, v in measurements.items()},
        library_heartbeats_by_lemma=library_costs,
        library_heartbeats=sum(library_costs.values()),
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('project', type=Path, help='prepared lean/ directory')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='rh-proof-reuse-') as temp:
        print(json.dumps(check(args.project.resolve(), Path(temp)), indent=2))


if __name__ == '__main__':
    main()

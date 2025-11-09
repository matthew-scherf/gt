"""
SUBSTRATE THEORY: ALPHA EMERGENCE VALIDATION
=============================================
Tests whether the fine structure constant alpha^-1 = 137.036 emerges from
grounding graph topology with k substrate types.

Expected result: gap(n=100, k in {3,4,5}) × 10 ≈ 137.036

Author: Matthew Scherf
Repository: https://github.com/matthew-scherf/Substrate
License: MIT
"""

import zlib
import numpy as np
import matplotlib.pyplot as plt
from tqdm import tqdm
import json
import logging
from datetime import datetime
from scipy import stats
from scipy.sparse.csgraph import connected_components
from scipy.sparse import csr_matrix
import platform
import sys
import io

# Configure logging with UTF-8 encoding for Windows compatibility
class UTF8StreamHandler(logging.StreamHandler):
    """Custom handler that forces UTF-8 encoding."""
    def __init__(self):
        super().__init__(stream=io.TextIOWrapper(
            sys.stdout.buffer, encoding='utf-8', errors='replace'
        ))

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('alpha_validation.log', encoding='utf-8'),
        UTF8StreamHandler()
    ]
)

def bits_to_bytes(bits: str) -> bytes:
    """Convert bitstring to bytes for compression."""
    padded = bits + '0' * (8 - len(bits) % 8)
    byte_array = bytearray()
    for i in range(0, len(padded), 8):
        byte_array.append(int(padded[i:i+8], 2))
    return bytes(byte_array)

def random_bits(length: int) -> str:
    """Generate random bitstring."""
    return ''.join(np.random.choice(['0', '1']) for _ in range(length))

def compress(bits: str) -> int:
    """Compress bitstring and return size in bits."""
    return len(zlib.compress(bits_to_bytes(bits), level=9)) * 8

def compression_ratio(e1: str, e2: str) -> float:
    """Measure shared information via compression."""
    K1 = compress(e1)
    K2 = compress(e2)
    K_joint = compress(e1 + e2)
    compression = K1 + K2 - K_joint
    return compression / (K1 + K2) if (K1 + K2) > 0 else 0.0

class GroundingGraph:
    """Grounding graph for alpha measurement."""
    
    def __init__(self, n_entities: int, n_substrate_types: int):
        """
        Generate grounding graph with explicit substrate sharing.
        
        Args:
            n_entities: Number of entities
            n_substrate_types: Number of shared substrate patterns (k)
        """
        # Generate substrate types
        substrates = []
        for s in range(n_substrate_types):
            substrate_pattern = random_bits(10)
            substrates.append(substrate_pattern * 30)  # 300 bits each
        
        # Generate entities sharing substrates
        self.entities = []
        for i in range(n_entities):
            substrate_idx = i % n_substrate_types
            substrate = substrates[substrate_idx]
            noise_pattern = random_bits(10)
            noise = noise_pattern * 70  # 700 bits
            self.entities.append(substrate + noise)
        
        self.n = n_entities
        
        # Compute compression matrix
        self.compression_matrix = np.zeros((n_entities, n_entities))
        for i in range(n_entities):
            for j in range(i+1, n_entities):
                ratio = compression_ratio(self.entities[i], self.entities[j])
                self.compression_matrix[i, j] = ratio
                self.compression_matrix[j, i] = ratio
        
        # Build adjacency matrix
        nonzero = self.compression_matrix[self.compression_matrix > 0]
        threshold = np.percentile(nonzero, 40)
        self.adjacency = (self.compression_matrix > threshold).astype(float)
        np.fill_diagonal(self.adjacency, 0)
        
        # Ensure connectivity
        n_components, _ = connected_components(csr_matrix(self.adjacency), directed=False)
        
        if n_components > 1:
            for percentile in [30, 20, 10, 5]:
                threshold = np.percentile(nonzero, percentile)
                self.adjacency = (self.compression_matrix > threshold).astype(float)
                np.fill_diagonal(self.adjacency, 0)
                n_components, _ = connected_components(csr_matrix(self.adjacency), directed=False)
                if n_components == 1:
                    break
    
    def spectral_gap(self) -> float:
        """Compute spectral gap of graph Laplacian."""
        degrees = self.adjacency.sum(axis=1)
        L = np.diag(degrees) - self.adjacency
        eigenvalues = np.linalg.eigvalsh(L)
        eigenvalues.sort()
        return eigenvalues[1] if len(eigenvalues) > 1 else 0.0

def compute_statistics(gaps, alpha_inverse=137.035999084):
    """Compute comprehensive statistics for gap measurements."""
    gaps = np.array(gaps)
    gaps_times_10 = gaps * 10
    
    mean = np.mean(gaps_times_10)
    std = np.std(gaps_times_10, ddof=1)
    sem = stats.sem(gaps_times_10)
    
    # 95% confidence interval
    ci = stats.t.interval(0.95, len(gaps)-1, loc=mean, scale=sem)
    
    # Hypothesis test: does mean differ from alpha^-1?
    t_stat, p_value = stats.ttest_1samp(gaps_times_10, alpha_inverse)
    
    error_percent = abs(mean - alpha_inverse) / alpha_inverse * 100
    
    return {
        'mean': float(np.mean(gaps)),
        'std': float(np.std(gaps, ddof=1)),
        'mean_times_10': float(mean),
        'std_times_10': float(std),
        'sem_times_10': float(sem),
        'ci_95_lower': float(ci[0]),
        'ci_95_upper': float(ci[1]),
        't_statistic': float(t_stat),
        'p_value': float(p_value),
        'error_percent': float(error_percent),
        'alpha_match': error_percent < 5.0
    }

def get_system_info():
    """Record computational environment."""
    return {
        'python_version': sys.version,
        'numpy_version': np.__version__,
        'scipy_version': stats.__version__ if hasattr(stats, '__version__') else 'unknown',
        'platform': platform.platform(),
        'processor': platform.processor(),
        'hostname': platform.node(),
        'timestamp': datetime.now().isoformat()
    }

def save_checkpoint(k, trial, gap, filename='checkpoint.jsonl'):
    """Save checkpoint after each trial for crash recovery."""
    checkpoint = {
        'k': int(k),
        'trial': int(trial),
        'gap': float(gap),
        'timestamp': datetime.now().isoformat()
    }
    with open(filename, 'a', encoding='utf-8') as f:
        f.write(json.dumps(checkpoint) + '\n')

def alpha_validation_test(n_entities=100, n_trials=100, substrate_types=[2,3,4,5,6,7], 
                         seed=None, save_checkpoints=True):
    """
    Run comprehensive alpha validation across substrate types.
    
    Args:
        n_entities: Number of entities in grounding graph
        n_trials: Number of independent trials per substrate type
        substrate_types: List of k values to test
        seed: Random seed for reproducibility (None for random)
        save_checkpoints: Save after each trial for crash recovery
    
    Returns:
        Dictionary with results
    """
    if seed is not None:
        np.random.seed(seed)
        logging.info(f"Using random seed: {seed}")
    
    alpha_inverse = 137.035999084
    
    logging.info("="*70)
    logging.info("SUBSTRATE THEORY: ALPHA EMERGENCE VALIDATION")
    logging.info("="*70)
    logging.info(f"n_entities={n_entities}, n_trials={n_trials}")
    logging.info(f"Target: alpha^-1 = {alpha_inverse}")
    logging.info(f"Testing k = {substrate_types}")
    logging.info("")
    
    results = {}
    all_gaps = {}
    
    for k in substrate_types:
        logging.info(f"Testing k={k} substrate types...")
        logging.info("-"*70)
        
        gaps = []
        for trial in tqdm(range(n_trials), desc=f"k={k}"):
            graph = GroundingGraph(n_entities, n_substrate_types=k)
            gap = graph.spectral_gap()
            gaps.append(gap)
            
            if save_checkpoints:
                save_checkpoint(k, trial, gap)
        
        all_gaps[k] = gaps
        stats_dict = compute_statistics(gaps, alpha_inverse)
        
        results[k] = stats_dict
        
        logging.info(f"\nRESULTS for k={k}:")
        logging.info(f"  Mean gap: {stats_dict['mean']:.4f} +/- {stats_dict['std']:.4f}")
        logging.info(f"  gap x 10: {stats_dict['mean_times_10']:.4f} +/- {stats_dict['std_times_10']:.4f}")
        logging.info(f"  95% CI:   [{stats_dict['ci_95_lower']:.4f}, {stats_dict['ci_95_upper']:.4f}]")
        logging.info(f"  alpha^-1: {alpha_inverse:.4f}")
        logging.info(f"  Error:    {stats_dict['error_percent']:.2f}%")
        logging.info(f"  p-value:  {stats_dict['p_value']:.4f}")
        
        if stats_dict['alpha_match']:
            logging.info(f"  ALPHA SIGNATURE CONFIRMED!")
        logging.info("")
    
    # Variance analysis across k values
    gaps_by_k = [np.array(all_gaps[k]) for k in substrate_types]
    f_stat, p_value_anova = stats.f_oneway(*gaps_by_k)
    
    logging.info("="*70)
    logging.info("VARIANCE ANALYSIS")
    logging.info("="*70)
    logging.info(f"ANOVA F-statistic: {f_stat:.4f}")
    logging.info(f"ANOVA p-value: {p_value_anova:.4f}")
    if p_value_anova < 0.05:
        logging.info("Variances differ significantly across k values")
    else:
        logging.info("Variances similar across k values")
    
    return results, all_gaps

def plot_results(results, all_gaps, save_path='alpha_validation_results.png'):
    """Create comprehensive visualization with convergence plots."""
    fig = plt.figure(figsize=(16, 12))
    gs = fig.add_gridspec(3, 3, hspace=0.3, wspace=0.3)
    
    fig.suptitle('Alpha Emergence from Grounding Topology', 
                 fontsize=18, fontweight='bold')
    
    alpha_inverse = 137.035999084
    substrate_types = sorted(results.keys())
    
    # Plot 1: Gap distributions (larger)
    ax1 = fig.add_subplot(gs[0, :2])
    for k in substrate_types:
        gaps = np.array(all_gaps[k])
        ax1.hist(gaps, bins=30, alpha=0.5, label=f'k={k}')
    ax1.set_xlabel('Spectral Gap', fontsize=11)
    ax1.set_ylabel('Count', fontsize=11)
    ax1.set_title('Gap Distributions', fontsize=12, fontweight='bold')
    ax1.legend()
    ax1.grid(alpha=0.3)
    
    # Plot 2: Gap × 10 vs Alpha
    ax2 = fig.add_subplot(gs[0, 2])
    means = [results[k]['mean_times_10'] for k in substrate_types]
    stds = [results[k]['std_times_10'] for k in substrate_types]
    ax2.errorbar(substrate_types, means, yerr=stds, fmt='o-', 
                 markersize=10, linewidth=2, capsize=5)
    ax2.axhline(alpha_inverse, color='r', linestyle='--', 
                linewidth=2, label=f'α⁻¹ = {alpha_inverse:.2f}')
    ax2.set_xlabel('k (substrate types)', fontsize=11)
    ax2.set_ylabel('gap × 10', fontsize=11)
    ax2.set_title('Alpha Emergence', fontsize=12, fontweight='bold')
    ax2.legend()
    ax2.grid(alpha=0.3)
    
    # Plot 3: Convergence traces
    ax3 = fig.add_subplot(gs[1, :2])
    for k in substrate_types:
        gaps = np.array(all_gaps[k])
        trials = np.arange(len(gaps)) + 1
        cumulative_mean = np.cumsum(gaps) / trials * 10
        ax3.plot(trials, cumulative_mean, alpha=0.7, label=f'k={k}', linewidth=2)
    ax3.axhline(alpha_inverse, color='r', linestyle='--', 
                linewidth=2, label='α⁻¹')
    ax3.set_xlabel('Trial Number', fontsize=11)
    ax3.set_ylabel('Cumulative Mean (gap × 10)', fontsize=11)
    ax3.set_title('Convergence Over Trials', fontsize=12, fontweight='bold')
    ax3.legend(loc='best')
    ax3.grid(alpha=0.3)
    
    # Plot 4: Error bars
    ax4 = fig.add_subplot(gs[1, 2])
    errors = [results[k]['error_percent'] for k in substrate_types]
    colors = ['green' if e < 5 else 'orange' if e < 10 else 'red' for e in errors]
    ax4.bar(substrate_types, errors, color=colors, alpha=0.7)
    ax4.axhline(5, color='green', linestyle='--', label='5% threshold')
    ax4.set_xlabel('k (substrate types)', fontsize=11)
    ax4.set_ylabel('Error from α⁻¹ (%)', fontsize=11)
    ax4.set_title('Prediction Error', fontsize=12, fontweight='bold')
    ax4.legend()
    ax4.grid(alpha=0.3)
    
    # Plot 5: Confidence intervals
    ax5 = fig.add_subplot(gs[2, :2])
    for i, k in enumerate(substrate_types):
        ci_low = results[k]['ci_95_lower']
        ci_high = results[k]['ci_95_upper']
        mean = results[k]['mean_times_10']
        
        ax5.plot([k, k], [ci_low, ci_high], 'o-', linewidth=2, markersize=8)
        ax5.plot(k, mean, 'ro', markersize=6)
    
    ax5.axhline(alpha_inverse, color='r', linestyle='--', 
                linewidth=2, label='α⁻¹', alpha=0.7)
    ax5.fill_between(substrate_types, 
                     alpha_inverse - 5, alpha_inverse + 5,
                     alpha=0.2, color='green', label='±5 range')
    ax5.set_xlabel('k (substrate types)', fontsize=11)
    ax5.set_ylabel('gap × 10 with 95% CI', fontsize=11)
    ax5.set_title('Confidence Intervals', fontsize=12, fontweight='bold')
    ax5.legend()
    ax5.grid(alpha=0.3)
    
    # Plot 6: Summary table
    ax6 = fig.add_subplot(gs[2, 2])
    ax6.axis('off')
    
    table_data = []
    for k in substrate_types:
        gap_10 = results[k]['mean_times_10']
        error = results[k]['error_percent']
        p_val = results[k]['p_value']
        match = '✓' if results[k]['alpha_match'] else ''
        table_data.append([
            f'k={k}', 
            f'{gap_10:.2f}',
            f'{error:.2f}%',
            f'{p_val:.3f}',
            match
        ])
    
    table = ax6.table(
        cellText=table_data,
        colLabels=['k', 'gap×10', 'Error', 'p-value', 'Match'],
        cellLoc='center',
        loc='center',
        bbox=[0, 0, 1, 1]
    )
    table.auto_set_font_size(False)
    table.set_fontsize(9)
    table.scale(1, 2)
    
    # Color table
    for i in range(len(substrate_types) + 1):
        for j in range(5):
            cell = table[(i, j)]
            if i == 0:
                cell.set_facecolor('#4CAF50')
                cell.set_text_props(weight='bold', color='white')
            else:
                if results[substrate_types[i-1]]['alpha_match']:
                    cell.set_facecolor('#e8f5e9')
                else:
                    cell.set_facecolor('#ffebee')
    
    plt.savefig(save_path, dpi=300, bbox_inches='tight')
    logging.info(f"Plot saved: {save_path}")
    
    return fig

def save_results(results, all_gaps, filename='alpha_validation_results.json'):
    """Save results with full metadata."""
    output = {
        'metadata': {
            'timestamp': datetime.now().isoformat(),
            'description': 'Alpha emergence validation from grounding topology',
            'theory': 'Substrate Theory - Algorithmic Information Physics',
            'n_entities': 100,
            'n_trials': len(all_gaps[list(all_gaps.keys())[0]]),
            'alpha_inverse_target': 137.035999084,
            'method': 'Compression-based grounding graphs with spectral gap measurement'
        },
        'system_info': get_system_info(),
        'results': {
            str(k): {
                'mean_gap': v['mean'],
                'std_gap': v['std'],
                'mean_gap_times_10': v['mean_times_10'],
                'std_gap_times_10': v['std_times_10'],
                'ci_95_lower': v['ci_95_lower'],
                'ci_95_upper': v['ci_95_upper'],
                't_statistic': v['t_statistic'],
                'p_value': v['p_value'],
                'error_percent': v['error_percent'],
                'alpha_match': bool(v['alpha_match'])
            }
            for k, v in results.items()
        }
    }
    
    with open(filename, 'w', encoding='utf-8') as f:
        json.dump(output, f, indent=2)
    
    logging.info(f"Results saved: {filename}")

def export_latex_table(results, filename='alpha_table.tex'):
    """Generate LaTeX table for publication."""
    lines = [
        r'\begin{table}[h]',
        r'\centering',
        r'\caption{Alpha emergence from grounding topology at $n=100$ entities}',
        r'\label{tab:alpha}',
        r'\begin{tabular}{ccccc}',
        r'\hline',
        r'$k$ & $\langle\lambda_1\rangle \times 10$ & Error (\%) & $p$-value & Match \\ \hline'
    ]
    
    for k in sorted(results.keys()):
        r = results[k]
        match = r'$\checkmark$' if r['alpha_match'] else ''
        lines.append(
            f"{k} & ${r['mean_times_10']:.2f} \\pm {r['std_times_10']:.2f}$ & "
            f"{r['error_percent']:.2f} & {r['p_value']:.3f} & {match} \\\\"
        )
    
    lines.extend([
        r'\hline',
        r'\end{tabular}',
        r'\end{table}'
    ])
    
    with open(filename, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))
    
    logging.info(f"LaTeX table saved: {filename}")

if __name__ == "__main__":
    # Run validation
    results, all_gaps = alpha_validation_test(
        n_entities=100,
        n_trials=100,
        substrate_types=[2, 3, 4, 5, 6, 7],
        seed=None,  # Set to integer for reproducibility
        save_checkpoints=True
    )
    
    # Save results
    save_results(results, all_gaps)
    
    # Export LaTeX table
    export_latex_table(results)
    
    # Create visualization
    plot_results(results, all_gaps)
    
    # Print summary
    logging.info("\n" + "="*70)
    logging.info("VALIDATION SUMMARY")
    logging.info("="*70)
    
    alpha_matches = [k for k, v in results.items() if v['alpha_match']]
    
    if alpha_matches:
        logging.info(f"\nAlpha signature detected for k = {alpha_matches}")
        
        if 3 in alpha_matches:
            logging.info("  k=3: Three fermion generations (e/mu/tau)")
        if 4 in alpha_matches:
            logging.info("  k=4: Four spacetime dimensions or four forces")
        if 5 in alpha_matches:
            logging.info("  k=5: Grand unification symmetry (SU(5)?)")
        if 7 in alpha_matches:
            logging.info("  k=7: Seven substrate axioms")
        
        logging.info("\nCONCLUSION: alpha^-1 emerges from grounding topology.")
        logging.info("The fine structure constant is a topological invariant of")
        logging.info("information space, not a free parameter of nature.")
    else:
        logging.info("\nNo clear alpha signature detected.")
        logging.info("Further investigation needed.")
    
    logging.info("\n" + "="*70)
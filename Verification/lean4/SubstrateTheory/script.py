import zlib
import numpy as np
import matplotlib.pyplot as plt
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import eigsh
from scipy.sparse.csgraph import connected_components
from tqdm import tqdm
import networkx as nx

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

def generate_compressible_entity(pattern_length=10, repetitions=100):
    """Generate entity with internal structure."""
    pattern = random_bits(pattern_length)
    return pattern * repetitions

def compression_ratio(e1: str, e2: str) -> float:
    """Measure shared information via compression."""
    K1 = compress(e1)
    K2 = compress(e2)
    K_joint = compress(e1 + e2)
    compression = K1 + K2 - K_joint
    return compression / (K1 + K2) if (K1 + K2) > 0 else 0.0

def grounds(e1: str, e2: str, threshold: float = 0.20) -> bool:
    """Check if e1 grounds e2 (they share significant structure)."""
    return compression_ratio(e1, e2) > threshold

class GroundingGraph:
    """Grounding graph with topological measurements."""
    
    def __init__(self, n_entities: int, n_substrate_types: int = 3):
        """Generate grounding graph with n entities."""
        print(f"Generating {n_entities} entities...")
        
        # Generate entities with explicit substrate sharing
        # Create 3 substrate types (mimics 3 fermion generations!)
        
        substrates = []
        for s in range(n_substrate_types):
            # Each substrate is 300 bits (30% of entity)
            substrate_pattern = random_bits(10)
            substrates.append(substrate_pattern * 30)  # 300 bits
            
        self.entities = []
        for i in range(n_entities):
            # Entities share substrate in groups
            substrate_idx = i % n_substrate_types
            substrate = substrates[substrate_idx]
            
            # Add unique noise (700 bits = 70% of entity)
            noise_pattern = random_bits(10)
            noise = noise_pattern * 70  # 700 bits
            
            entity = substrate + noise
            self.entities.append(entity)
        
        self.n = n_entities
        
        # Compute compression matrix
        print("Computing pairwise compressions...")
        self.compression_matrix = np.zeros((n_entities, n_entities))
        
        pairs = [(i, j) for i in range(n_entities) for j in range(i+1, n_entities)]
        for i, j in tqdm(pairs, desc="Compression calculations"):
            ratio = compression_ratio(self.entities[i], self.entities[j])
            self.compression_matrix[i, j] = ratio
            self.compression_matrix[j, i] = ratio
        
        # Use adaptive threshold - compute ONCE after matrix is built
        nonzero_compressions = self.compression_matrix[self.compression_matrix > 0]
        self.grounding_threshold = np.percentile(nonzero_compressions, 40)
        print(f"Using threshold: {self.grounding_threshold:.4f} (targets ~50-70% connectivity)")
        
        # Build adjacency matrix
        self.adjacency = (self.compression_matrix > self.grounding_threshold).astype(float)
        
        # Remove self-loops
        np.fill_diagonal(self.adjacency, 0)
        
        n_edges = int(self.adjacency.sum()/2)
        print(f"Graph constructed: {n_entities} nodes, {n_edges} edges")
        
        # Check connectivity
        n_components, _ = connected_components(csr_matrix(self.adjacency), directed=False)
        if n_components > 1:
            print(f"  Warning: Graph has {n_components} components. Lowering threshold...")
            # Lower threshold until connected
            for percentile in [30, 20, 10, 5]:
                self.grounding_threshold = np.percentile(nonzero_compressions, percentile)
                self.adjacency = (self.compression_matrix > self.grounding_threshold).astype(float)
                np.fill_diagonal(self.adjacency, 0)
                n_components, _ = connected_components(csr_matrix(self.adjacency), directed=False)
                if n_components == 1:
                    n_edges = int(self.adjacency.sum()/2)
                    print(f"  Connected at threshold {self.grounding_threshold:.4f} ({n_edges} edges)")
                    break
    
    def spectral_gap(self) -> float:
        """Compute spectral gap of graph Laplacian."""
        print("Computing spectral gap...")
        
        # Build Laplacian
        degrees = self.adjacency.sum(axis=1)
        L = np.diag(degrees) - self.adjacency
        
        # Compute smallest non-zero eigenvalue
        eigenvalues = np.linalg.eigvalsh(L)
        eigenvalues.sort()
        
        # Gap is second smallest (first is ~0 for connected components)
        gap = eigenvalues[1] if len(eigenvalues) > 1 else 0.0
        
        print(f"  Spectral gap: {gap:.6f}")
        return gap
    
    def estimate_dimension(self) -> float:
        """Estimate Hausdorff dimension via box-counting."""
        print("Estimating dimension...")
        
        # Use compression matrix as distance metric
        distances = 1 - self.compression_matrix
        
        # Box-counting: count entities within radius r
        radii = np.linspace(0.1, 0.9, 10)
        counts = []
        
        for r in radii:
            # Count entities within radius r of each entity
            within_radius = (distances < r).sum(axis=1)
            counts.append(np.mean(within_radius))
        
        # Fit power law: count ~ r^dimension
        log_r = np.log(radii)
        log_count = np.log(counts)
        
        # Linear fit
        coeffs = np.polyfit(log_r, log_count, 1)
        dimension = coeffs[0]
        
        print(f"  Estimated dimension: {dimension:.2f}")
        return dimension
    
    def compute_symmetries(self) -> dict:
        """Detect symmetry structure using networkx."""
        print("Computing symmetries...")
        
        # Convert to networkx graph
        G = nx.from_numpy_array(self.adjacency)
        
        # Compute automorphism group size (expensive for large graphs)
        if self.n <= 50:
            try:
                from networkx.algorithms import isomorphism
                matcher = isomorphism.GraphMatcher(G, G)
                automorphisms = list(matcher.isomorphisms_iter())
                n_automorphisms = len(automorphisms)
            except:
                n_automorphisms = 1
        else:
            n_automorphisms = None  # Too expensive
        
        # Compute other symmetry indicators
        clustering = nx.average_clustering(G)
        transitivity = nx.transitivity(G)
        
        symmetries = {
            'n_automorphisms': n_automorphisms,
            'clustering_coefficient': clustering,
            'transitivity': transitivity
        }
        
        print(f"  Clustering: {clustering:.4f}, Transitivity: {transitivity:.4f}")
        return symmetries
    
    def connectivity_analysis(self) -> dict:
        """Analyze connected components."""
        print("Analyzing connectivity...")
        
        n_components, labels = connected_components(
            csr_matrix(self.adjacency), directed=False
        )
        
        # Component sizes
        component_sizes = [np.sum(labels == i) for i in range(n_components)]
        largest_component = max(component_sizes)
        
        connectivity = {
            'n_components': n_components,
            'largest_component_size': largest_component,
            'largest_component_fraction': largest_component / self.n
        }
        
        print(f"  Components: {n_components}, Largest: {largest_component}/{self.n}")
        return connectivity
    
    def full_analysis(self) -> dict:
        """Run all topological measurements."""
        results = {}
        
        results['n_entities'] = self.n
        results['n_edges'] = int(self.adjacency.sum() / 2)
        results['edge_density'] = results['n_edges'] / (self.n * (self.n - 1) / 2)
        
        results['spectral_gap'] = self.spectral_gap()
        results['dimension'] = self.estimate_dimension()
        results['connectivity'] = self.connectivity_analysis()
        # results['symmetries'] = self.compute_symmetries()  # Skip - too slow for dense graphs
        results['symmetries'] = {'clustering_coefficient': 0, 'transitivity': 0}  # Placeholder
        
        return results

def scaling_experiment(sizes=[50, 100, 200], trials=3):
    """Test how topology scales with graph size."""
    print("="*60)
    print("PHASE 1: SCALING EXPERIMENT")
    print("="*60)
    
    results = []
    
    for n in sizes:
        print(f"\n{'='*60}")
        print(f"Testing n={n} entities ({trials} trials)")
        print(f"{'='*60}")
        
        for trial in range(trials):
            print(f"\nTrial {trial+1}/{trials}")
            print("-"*60)
            
            graph = GroundingGraph(n)
            analysis = graph.full_analysis()
            analysis['trial'] = trial
            results.append(analysis)
    
    return results

def analyze_convergence(results):
    """Check if topology converges as n increases."""
    print("\n" + "="*60)
    print("CONVERGENCE ANALYSIS")
    print("="*60)
    
    # Group by size
    sizes = sorted(set(r['n_entities'] for r in results))
    
    print(f"\n{'Size':<10} {'Gap':<15} {'Dimension':<15} {'Density':<15}")
    print("-"*60)
    
    for n in sizes:
        subset = [r for r in results if r['n_entities'] == n]
        
        gaps = [r['spectral_gap'] for r in subset]
        dims = [r['dimension'] for r in subset]
        densities = [r['edge_density'] for r in subset]
        
        gap_mean = np.mean(gaps)
        gap_std = np.std(gaps)
        
        dim_mean = np.mean(dims)
        dim_std = np.std(dims)
        
        density_mean = np.mean(densities)
        
        print(f"{n:<10} {gap_mean:.4f}±{gap_std:.4f}  {dim_mean:.2f}±{dim_std:.2f}      {density_mean:.4f}")
    
    # Test for convergence
    print("\n" + "="*60)
    print("CONVERGENCE TESTS")
    print("="*60)
    
    # Check if spectral gap stabilizes
    gaps_by_size = [[r['spectral_gap'] for r in results if r['n_entities'] == n] for n in sizes]
    
    if len(sizes) >= 2:
        # Compare last two sizes
        from scipy.stats import ttest_ind
        t_stat, p_value = ttest_ind(gaps_by_size[-2], gaps_by_size[-1])
        
        print(f"\nSpectral gap stability (last two sizes): p={p_value:.4f}")
        if p_value > 0.05:
            print("  ✓ STABLE: Gap not significantly different between sizes")
        else:
            print("  ○ EVOLVING: Gap still changing with size")
    
    # Check for alpha signature
    print("\n" + "="*60)
    print("PHYSICAL CONSTANT SIGNATURES")
    print("="*60)
    
    alpha_inverse = 137.035999084
    
    for n in sizes:
        subset = [r for r in results if r['n_entities'] == n]
        gap_mean = np.mean([r['spectral_gap'] for r in subset])
        
        # Test various relationships to alpha
        ratios = {
            'gap': gap_mean,
            'gap^-1': 1/gap_mean if gap_mean > 0 else 0,
            'gap * n': gap_mean * n,
            'gap * n^0.5': gap_mean * np.sqrt(n),
        }
        
        print(f"\nn={n}:")
        for name, value in ratios.items():
            ratio_to_alpha = value / alpha_inverse if alpha_inverse > 0 else 0
            match = abs(value - alpha_inverse) / alpha_inverse < 0.1
            
            print(f"  {name:<15} = {value:8.2f}  (ratio to α⁻¹: {ratio_to_alpha:.3f}) {'✓' if match else ''}")

# Visualization
def plot_results(results):
    """Visualize scaling behavior."""
    sizes = sorted(set(r['n_entities'] for r in results))
    
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))
    fig.suptitle('Phase 1: Grounding Graph Topology', fontsize=14)
    
    # Spectral gap vs size
    ax = axes[0, 0]
    for n in sizes:
        gaps = [r['spectral_gap'] for r in results if r['n_entities'] == n]
        ax.scatter([n]*len(gaps), gaps, alpha=0.6, s=50)
    ax.set_xlabel('Graph Size (n)')
    ax.set_ylabel('Spectral Gap')
    ax.set_title('Spectral Gap Scaling')
    ax.grid(alpha=0.3)
    
    # Dimension vs size
    ax = axes[0, 1]
    for n in sizes:
        dims = [r['dimension'] for r in results if r['n_entities'] == n]
        ax.scatter([n]*len(dims), dims, alpha=0.6, s=50)
    ax.axhline(y=4, color='r', linestyle='--', label='Expected (3+1)D')
    ax.set_xlabel('Graph Size (n)')
    ax.set_ylabel('Estimated Dimension')
    ax.set_title('Dimension Estimation')
    ax.legend()
    ax.grid(alpha=0.3)
    
    # Edge density vs size
    ax = axes[1, 0]
    for n in sizes:
        densities = [r['edge_density'] for r in results if r['n_entities'] == n]
        ax.scatter([n]*len(densities), densities, alpha=0.6, s=50)
    ax.set_xlabel('Graph Size (n)')
    ax.set_ylabel('Edge Density')
    ax.set_title('Graph Density Scaling')
    ax.grid(alpha=0.3)
    
    # Largest component fraction
    ax = axes[1, 1]
    for n in sizes:
        fractions = [r['connectivity']['largest_component_fraction'] 
                    for r in results if r['n_entities'] == n]
        ax.scatter([n]*len(fractions), fractions, alpha=0.6, s=50)
    ax.set_xlabel('Graph Size (n)')
    ax.set_ylabel('Largest Component Fraction')
    ax.set_title('Connectivity')
    ax.grid(alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('phase1_topology.png', dpi=150)
    print("\nPlot saved as 'phase1_topology.png'")
    plt.show()
    def test_substrate_variations():
     """Test different substrate counts at n=100."""
    print("\n" + "="*60)
    print("SUBSTRATE VARIATION TEST")
    print("="*60)
    
    results = []
    
    for k_substrates in [2, 3, 4, 5, 6]:
        print(f"\nTesting k={k_substrates} substrates at n=100")
        print("-"*60)
        
        gaps_for_k = []
        
        for trial in range(10):
            print(f"  Trial {trial+1}/10...", end=" ")
            graph = GroundingGraph(n_entities=100, n_substrate_types=k_substrates)
            gap = graph.spectral_gap()
            gaps_for_k.append(gap)
            print(f"gap={gap:.4f}")
            
            results.append({
                'n': 100,
                'k_substrates': k_substrates,
                'trial': trial,
                'gap': gap,
                'gap_times_10': gap * 10,
                'error_from_alpha': abs(gap * 10 - 137.036) / 137.036
            })
        
        mean_gap = np.mean(gaps_for_k)
        std_gap = np.std(gaps_for_k)
        mean_times_10 = mean_gap * 10
        error = abs(mean_times_10 - 137.036) / 137.036 * 100
        
        print(f"\n  k={k_substrates} SUMMARY:")
        print(f"    Mean gap: {mean_gap:.4f} ± {std_gap:.4f}")
        print(f"    gap × 10: {mean_times_10:.4f}")
        print(f"    Error from α⁻¹: {error:.2f}%")
        
        match = "✓✓✓" if error < 1 else "✓✓" if error < 5 else "✓" if error < 10 else ""
        if match:
            print(f"    {match} ALPHA SIGNATURE DETECTED!")
    
    # Summary table
    print("\n" + "="*60)
    print("SUMMARY: gap × 10 vs α⁻¹ = 137.036")
    print("="*60)
    print(f"{'k_substrates':<15} {'mean(gap×10)':<15} {'error %':<15} {'match':<10}")
    print("-"*60)
    
    for k in [2, 3, 4, 5, 6]:
        k_results = [r for r in results if r['k_substrates'] == k]
        mean_val = np.mean([r['gap_times_10'] for r in k_results])
        error = abs(mean_val - 137.036) / 137.036 * 100
        match = "✓✓✓" if error < 1 else "✓✓" if error < 5 else "✓" if error < 10 else ""
        print(f"{k:<15} {mean_val:<15.4f} {error:<15.2f} {match:<10}")
    
    return results
if __name__ == "__main__":
    # Run scaling experiment
    results = scaling_experiment(sizes=[50, 100, 200, 400, 800], trials=5)
    
    # Analyze convergence
    analyze_convergence(results)
    # Test for alpha relationship
print("\n" + "="*60)
print("DETAILED ALPHA INVESTIGATION")
print("="*60)

alpha_inv = 137.035999084

# Group results by size
for size in sorted(set(r['n_entities'] for r in results)):
    size_results = [r for r in results if r['n_entities'] == size]
    gaps = [r['spectral_gap'] for r in size_results]
    mean_gap = np.mean(gaps)
    
    print(f"\nn = {size}:")
    print(f"  Mean gap: {mean_gap:.6f}")
    print(f"  Std gap:  {np.std(gaps):.6f}")
    
    # Test many possible relationships
    tests = [
        ('gap', mean_gap),
        ('gap²', mean_gap**2),
        ('gap³', mean_gap**3),
        ('√gap', np.sqrt(mean_gap)),
        ('gap × log(n)', mean_gap * np.log(size)),
        ('gap × √n', mean_gap * np.sqrt(size)),
        ('gap × n / 10', mean_gap * size / 10),
        ('n / gap', size / mean_gap if mean_gap > 0 else 0),
        ('n² / gap', size**2 / mean_gap if mean_gap > 0 else 0),
        ('(gap × n)^(1/3)', (mean_gap * size)**(1/3)),
    ]
    
    for name, value in tests:
        error = abs(value - alpha_inv) / alpha_inv
        match = '✓✓✓' if error < 0.01 else '✓✓' if error < 0.05 else '✓' if error < 0.10 else ''
        print(f"    {name:20s} = {value:10.4f}  (error: {error*100:5.2f}%)  {match}")
    # Visualize
    plot_results(results)
    
    print("\n" + "="*60)
    print("PHASE 1 COMPLETE")
    print("="*60)
    print("\nNext steps:")
    print("1. If topology converges → proceed to Phase 2 (gauge symmetry extraction)")
    print("2. If topology evolving → test larger sizes (500, 1000)")
    print("3. If alpha signature detected → investigate relationship")
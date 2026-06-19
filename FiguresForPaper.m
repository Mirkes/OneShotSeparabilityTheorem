%%%%%%%%%%%%%%%
%
% Script to form figure 2 of paper.
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%%%


% Figure 2
% Common set of parameters
distrs = {"Uniform in cubes", "Gaussian", "Product of exponential",...
    "Product of Laplace", "Product of Pareto"};
dist = ["Cube", "Gauss", "Exp", "Laplace", "Pareto"];
nDist = length(dist);
legs = {"Theoretical one-shot", "Universal boundary",...
    "Empirical one-shot", "Fisher $c_i=x_i$", "General linear",...
    "Nonlinear neural network",...
    "Universal formula $c_i=\frac{x_i}{1+|x_i|}$"};

% Line styles
styles = ["-", "-", ":", "--", "-", "-", ":"]; 
% Line colours
cols = ["#19A979", '#F5A623', "#2E86C1", "#E74C3C", "#34495E",...
    "#7D3C98", "#9B59B6"];
% Line width
widths = [2, 2, 2, 2, 2, 3, 2, 2];


figure("Position", [10, 10, 800, 700]);
t = tiledlayout(3, 2); % 3 rows, 2 columns
% Define reasonable intervals to avoid meaningless fragments
xlims = [5, 35; 5, 50; 5, 55; 5, 75; 5, 60];

for k = 1:nDist
    ax = nexttile;
    % Load data of this distribution
    load(dist(k) + "/SetData.mat");

    for kk = 1:numLines
        semilogy(dims, res(:, kk), styles(kk),...
            'LineWidth', widths(kk), "Color", cols(kk));
        hold on
    end
    % You can modify this interval as you like but usage of one interval is
    % very reasonable.
    ylim(ax, [0.95, 1000]); 
    xlim(ax, xlims(k, :));
    fontsize(gcf, 10, "points");
    xlabel("Dimension");
    if mod(k, 2) == 1
        ylabel("Separable set cardinality")
    end
    title(ax, distrs{k});
end

% Legend to position 6
lgd = legend(legs,'Interpreter','latex');
lgd.Layout.Tile = 6; 
fontsize(lgd, 12, "points");

% Add subplot labels
annotation('textbox', [0, 0.6, 0.1, 0.1], 'EdgeColor', 'none', 'String', 'a)');
annotation('textbox', [0.5, 0.6, 0.1, 0.1], 'EdgeColor', 'none', 'String', 'b)');
annotation('textbox', [0, 0.3, 0.1, 0.1], 'EdgeColor', 'none', 'String', 'c)');
annotation('textbox', [0.5, 0.3, 0.1, 0.1], 'EdgeColor', 'none', 'String', 'd)');
annotation('textbox', [0, 0, 0.1, 0.1], 'EdgeColor', 'none', 'String', 'e)');

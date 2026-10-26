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
legs = {"Theoretical one-shot", "Universal boundary","Empirical one-shot", "Fisher $c_i=x_i$", "General linear",...
    "Nonlinear neural network", "Universal formula $c_i=\frac{x_i}{1+|x_i|}$"};


styles = ["-", "-", ":", "--", "-", "-", ":"]; 
cols = ["#19A979", '#F5A623', "#2E86C1", "#E74C3C", "#34495E", "#7D3C98", "#9B59B6"];
widths = [2, 2, 2, 2, 2, 3, 2, 2];

% Form data
dims = [5:15,20:5:80]';
nDims = length(dims);

% Save data for figure
load("DataForFigures.mat");

% Now form figures

drawOrder = [6, 1, 2, 3, 4, 5, 7];

figure("Position", [10, 10, 800, 700]);
t = tiledlayout(3, 2); % 1 row, 2 columns
xlims = [5, 35; 5, 50; 5, 55; 5, 75; 5, 60];
numLines = 7;
legArr = gobjects(1, numLines);

for k = 1:nDist
    ax = nexttile;
    for kk = 1:numLines
        legArr(drawOrder(kk)) = semilogy(data{k, drawOrder(kk)}(:, 1),...
            data{k, drawOrder(kk)}(:, 2), styles(drawOrder(kk)),...
            'LineWidth', widths(drawOrder(kk)),...
            "Color", cols(drawOrder(kk)),...
            'DisplayName', legs{drawOrder(kk)});
        hold on
    end
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
lgd = legend(legArr,'Interpreter','latex');
lgd.Layout.Tile = 6; 
fontsize(lgd, 12, "points");

% Add subplot labels
annotation('textbox', [0, 0.6, 0.1, 0.1], 'EdgeColor', 'none', 'String', 'a)');
annotation('textbox', [0.5, 0.6, 0.1, 0.1], 'EdgeColor', 'none', 'String', 'b)');
annotation('textbox', [0, 0.3, 0.1, 0.1], 'EdgeColor', 'none', 'String', 'c)');
annotation('textbox', [0.5, 0.3, 0.1, 0.1], 'EdgeColor', 'none', 'String', 'd)');
annotation('textbox', [0, 0, 0.1, 0.1], 'EdgeColor', 'none', 'String', 'e)');

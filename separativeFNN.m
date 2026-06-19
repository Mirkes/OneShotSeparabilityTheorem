%%%%%%%%%%%%%
%
% Function to include NN into trainable wrapper
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%

function res = separativeFNN(dim, fisher, internalNet)
% separativeNN creates Separative Neural Network with specified set of
% parameters.
%
% Inputs:
%   dim is dimension of input vectors. Number of elements in two input
%       vectors is 2*n.
%   fisher is indicator of usage of Fisher direction as initial state. Must
%       be zero or False to use random initiation and any other value to
%       use Fisher's direction as initiation.
%   internalNet can be
%       omitted. In this case NN with one hidden layer with dim neurons and
%           Normalisation layer will be created. 
%       integer number. In this case three layers network will be created
%           with specified number of units in hidden layer, dim neurons in
%           the second layer and final Normalisation layer.
%       network to embed in SNN. There is some special requirements:
%           internalNet must be initialised.
%           internalNet must have one input unit with size dim.
%           internalNet must have one the last layer as the output one
%               with size dim.
%
% Output:
%   res is neural network with required structure.

    if nargin == 1
        fisher = True;
    else
        fisher = fisher > 0;
    end
    % Form list of layers for network
    lgraph = layerGraph(featureInputLayer(dim, Name="Y"));
    lgraph = addLayers(lgraph, featureInputLayer(dim, Name="aX"));

    % Work with given network
    if nargin < 3 
        % It will be linear NN
        gr = fullyConnectedLayer(dim, 'Name', 'internalNet1');
        if fisher
            gr.Weights = eye(dim);
        else
            gr.Weights = rand(dim);
        end
        gr.Bias = zeros(dim, 1);
        gr.WeightL2Factor = 0;
        layers = [featureInputLayer(dim, Name="internalNetIn"), ...
            gr, functionLayer(@(X) (X ./ vecnorm(X)), Name='Norm')];
        res = dlnetwork(layerGraph(layers));
        gr = networkLayer(res, Name='internalNet');
    elseif isnumeric(internalNet)
        % it is nonlinear NN
        gr = fullyConnectedLayer(internalNet, 'Name', 'internalNetH');
        grO = fullyConnectedLayer(dim, 'Name', 'internalNetOut');
        
        if ~fisher || internalNet < 2 * dim
            gr.Weights = rand(internalNet, dim);
            grO.Weights = rand(dim, internalNet);
        else
            gr.Weights = [eye(dim); -eye(dim); 0.001 * rand(internalNet - 2 * dim, dim)];
            grO.Weights = [eye(dim), -eye(dim), 0.001 * rand(dim, internalNet - 2 * dim)];
        end
        gr.Bias = zeros(internalNet, 1);
        grO.Bias = zeros(dim, 1);
        gr.WeightL2Factor = 0;
        layers = [featureInputLayer(dim, Name="internalNetIn"), ...
            gr, ...
            leakyReluLayer(0.01, Name="LRL"), ...
            grO,...
            functionLayer(@(X) (X ./ vecnorm(X)), Name='Norm')];
        res = dlnetwork(layerGraph(layers));
        gr = networkLayer(res, Name='internalNet');
    else
        % It is network created by somebody else
        gr = networkLayer(internalNet, Name='internalNet');
    end
    lgraph = addLayers(lgraph, gr);
    lgraph = connectLayers(lgraph, 'aX', 'internalNet');

    lgraph = addLayers(lgraph, subtractionLayer('SL'));
    lgraph = connectLayers(lgraph, 'Y', 'SL/in1');
    lgraph = connectLayers(lgraph, 'aX', 'SL/in2');

    lgraph = addLayers(lgraph, multiplicationLayer(2,'Name','mul'));
    lgraph = connectLayers(lgraph, 'SL', 'mul/in1');
    lgraph = connectLayers(lgraph, 'internalNet', 'mul/in2');
    
    fc = fullyConnectedLayer(2,'Name','FC');
    fc.Weights = [ones(1, dim); zeros(1, dim)];
    fc.Bias = [0; 0.0001];
    fc.WeightLearnRateFactor = 0;
    fc.BiasLearnRateFactor = 0;
    fc.WeightL2Factor = 0;
    fc.BiasL2Factor = 0;
    lgraph = addLayers(lgraph, fc);
    lgraph = connectLayers(lgraph, 'mul', 'FC');

    lgraph = addLayers(lgraph, softmaxLayer('Name', 'SM'));
    lgraph = connectLayers(lgraph, 'FC', 'SM');

    % Put weights to network
    res = dlnetwork(lgraph);
end

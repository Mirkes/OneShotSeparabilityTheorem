%%%%%%%%%%%%%
%
% Function to extract trained NN from wrapper
%
% Developed by Mirkes E.M. for paper Bogdan Grechuk, Alexander N. Gorban,
% Evgeny M. Mirkes, and Ivan Y. Tyukin. One short separation theorem
%
%%%%%%%%%%%%%

function res = extractionFromSNN(net)
% extractionFromSNN extracts NN that were wrapped to separative NN for
% training. Structure of separative NN is presented in readme.md and in
% paper.
%
% Inputs:
%   net is network that contains NN to extract
%
% Output:
%   res is extracted network

    lays = getLayer(net, 'internalNet');
    if isa(lays, 'nnet.cnn.layer.NetworkLayer')
        res = lays.Network;
        return
    end
    di = lays.InputSize;
    lgraph = layerGraph(featureInputLayer(di, Name="FInp"));
    lgraph = addLayers(lgraph, lays);
    lgraph = connectLayers(lgraph, 'FInp', 'internalNet');
    res = dlnetwork(lgraph);
end

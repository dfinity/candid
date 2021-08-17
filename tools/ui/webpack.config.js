const path = require("path");
const TerserPlugin = require("terser-webpack-plugin");
const dfxJson = require("./dfx.json");
const HtmlWebpackPlugin = require('html-webpack-plugin');
const CopyWebpackPlugin = require('copy-webpack-plugin');
const TsconfigPathsPlugin = require('tsconfig-paths-webpack-plugin');
const webpack = require("webpack");

// List of all aliases for canisters. This creates the module alias for
// the `import ... from "@dfinity/ic/canisters/xyz"` where xyz is the name of a
// canister.
const aliases = Object.entries(dfxJson.canisters).reduce(
  (acc, [name, _value]) => {
    // Get the network name, or `local` by default.
    const networkName = process.env["DFX_NETWORK"] || "local";
    const outputRoot = path.join(
      __dirname,
      ".dfx",
      networkName,
      "canisters",
      name
    );

    return {
      ...acc,
      ["dfx-generated/" + name]: path.join(outputRoot),
    };
  },
  {}
);

/**
 * Generate a webpack configuration for a canister.
 */
function generateWebpackConfigForCanister(name, info) {
  //if (typeof info.frontend !== "object") {
  //  return;
  //}

  return {
    mode: "production",
    entry: {
      index: path.join(__dirname, "src/index.ts"),
    },
    target: 'web',
    devtool: "source-map",
    optimization: {
      minimize: true,
      minimizer: [new TerserPlugin()],
    },
    resolve: {
      plugins: [new TsconfigPathsPlugin({ configFile: './tsconfig.json' })],
      extensions: [".js", ".ts", ".jsx", ".tsx"],
      fallback: {
        //"assert": require.resolve("assert/"),
        "buffer": require.resolve("buffer/"),
        //"events": require.resolve("events/"),
        //"stream": require.resolve("stream-browserify/"),
        //"util": require.resolve("util/"),        
      },
      alias: aliases,
    },
    output: {
      filename: "[name].js",
      path: path.join(__dirname, "dist", name),
    },

    // Depending in the language or framework you are using for
    // front-end development, add module loaders to the default
    // webpack configuration. For example, if you are using React
    // modules and CSS as described in the "Adding a stylesheet"
    // tutorial, uncomment the following lines:
    module: {
      rules: [
        { test: /\.css$/, use: ['style-loader','css-loader'] },
        {  test: /\.(jsx|ts|tsx)$/,
          use: {
            loader: "ts-loader",
            options: {
              // eslint-disable-next-line no-undef
              configFile: path.join(__dirname, 'tsconfig.json'),
              projectReferences: true,
            }
          }
        }
      ]
    },
    plugins: [
      new HtmlWebpackPlugin({
        template: 'src/candid.html',
        filename: 'index.html',
      }),
      new CopyWebpackPlugin({
        patterns: [
          {
            from: 'src/favicon.ico',
            to: 'favicon.ico',
          },
        ]}),
      new webpack.ProvidePlugin({
        Buffer: [require.resolve('buffer/'), 'Buffer'],
        //process: require.resolve('process/browser'),
      }),
    ],
  };
}

// If you have additional webpack configurations you want to build
//  as part of this configuration, add them to the section below.
module.exports = [
  ...Object.entries(dfxJson.canisters)
    .map(([name, info]) => {
      return generateWebpackConfigForCanister(name, info);
    })
    .filter((x) => !!x),
];
